import V185TrunkScan23Chunk0173

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1029601 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1029601 : Nat := 118140960795 + 1029601 * 2 ^ 59
def prefixEnd_1029601 : Nat := 4983230072969 + 3 ^ 40 * 1029601 * 2
def baseEnd_1029601 : Nat := 528680195349931415052457

theorem tailTrace_1029601 : CollatzResearch.WordTrace tailWord_1029601 prefixEnd_1029601 528680195349931415052457 := by
  unfold tailWord_1029601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37552633542938893696424657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25035089028625929130949771 37552633542938893696424657)
  ·
    refine ⟨28164475157204170272318493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37552633542938893696424657 28164475157204170272318493)
    ·
      refine ⟨10561678183951563852119435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28164475157204170272318493 10561678183951563852119435)
      ·
        refine ⟨15842517275927345778179153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561678183951563852119435 15842517275927345778179153)
        ·
          refine ⟨11881887956945509333634365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15842517275927345778179153 11881887956945509333634365)
          ·
            refine ⟨4455707983854566000112887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11881887956945509333634365 4455707983854566000112887)
            ·
              refine ⟨6683561975781849000169331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455707983854566000112887 6683561975781849000169331)
              ·
                refine ⟨10025342963672773500253997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683561975781849000169331 10025342963672773500253997)
                ·
                  refine ⟨3759503611377290062595249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025342963672773500253997 3759503611377290062595249)
                  ·
                    refine ⟨2819627708532967546946437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759503611377290062595249 2819627708532967546946437)
                    ·
                      refine ⟨528680195349931415052457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2819627708532967546946437 528680195349931415052457)
                      ·
                        rfl

theorem cell23_1029601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1029601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029601 prefixEnd_1029601 := by exact prefixLift 1029601
  have htrace : WordTrace (prefixWord ++ tailWord_1029601) baseStart_1029601 baseEnd_1029601 := by
    simpa [prefixWord, tailWord_1029601, baseEnd_1029601] using wordTrace_append hprefix tailTrace_1029601
  have hstable : (prefixWord ++ tailWord_1029601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029601).length < 2 ^ (prefixWord ++ tailWord_1029601).sum := by decide
  have hdescent : baseEnd_1029601 < baseStart_1029601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029662 : List Nat := [4, 3, 3, 1, 1, 1, 10]
def baseStart_1029662 : Nat := 118140960795 + 1029662 * 2 ^ 59
def prefixEnd_1029662 : Nat := 4983230072969 + 3 ^ 40 * 1029662 * 2
def baseEnd_1029662 : Nat := 6527302687282168844317

theorem tailTrace_1029662 : CollatzResearch.WordTrace tailWord_1029662 prefixEnd_1029662 6527302687282168844317 := by
  unfold tailWord_1029662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694357299464737639299405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25036572263811934076263493 4694357299464737639299405)
  ·
    refine ⟨1760383987299276614737277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4694357299464737639299405 1760383987299276614737277)
    ·
      refine ⟨660143995237228730526479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1760383987299276614737277 660143995237228730526479)
      ·
        refine ⟨990215992855843095789719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660143995237228730526479 990215992855843095789719)
        ·
          refine ⟨1485323989283764643684579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990215992855843095789719 1485323989283764643684579)
          ·
            refine ⟨2227985983925646965526869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485323989283764643684579 2227985983925646965526869)
            ·
              refine ⟨6527302687282168844317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2227985983925646965526869 6527302687282168844317)
              ·
                rfl

theorem cell23_1029662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 10].length) (baseStart_1029662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029662 prefixEnd_1029662 := by exact prefixLift 1029662
  have htrace : WordTrace (prefixWord ++ tailWord_1029662) baseStart_1029662 baseEnd_1029662 := by
    simpa [prefixWord, tailWord_1029662, baseEnd_1029662] using wordTrace_append hprefix tailTrace_1029662
  have hstable : (prefixWord ++ tailWord_1029662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029662).length < 2 ^ (prefixWord ++ tailWord_1029662).sum := by decide
  have hdescent : baseEnd_1029662 < baseStart_1029662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029672 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1029672 : Nat := 118140960795 + 1029672 * 2 ^ 59
def prefixEnd_1029672 : Nat := 4983230072969 + 3 ^ 40 * 1029672 * 2
def baseEnd_1029672 : Nat := 528716652476400637264631

theorem tailTrace_1029672 : CollatzResearch.WordTrace tailWord_1029672 prefixEnd_1029672 528716652476400637264631 := by
  unfold tailWord_1029672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777611562840836411129635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25036815417121115214839513 18777611562840836411129635)
  ·
    refine ⟨28166417344261254616694453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18777611562840836411129635 28166417344261254616694453)
    ·
      refine ⟨2640601626024492620315105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28166417344261254616694453 2640601626024492620315105)
      ·
        refine ⟨1980451219518369465236329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2640601626024492620315105 1980451219518369465236329)
        ·
          refine ⟨1485338414638777098927247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1980451219518369465236329 1485338414638777098927247)
          ·
            refine ⟨2228007621958165648390871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485338414638777098927247 2228007621958165648390871)
            ·
              refine ⟨3342011432937248472586307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228007621958165648390871 3342011432937248472586307)
              ·
                refine ⟨5013017149405872708879461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342011432937248472586307 5013017149405872708879461)
                ·
                  refine ⟨939940715513601132914899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5013017149405872708879461 939940715513601132914899)
                  ·
                    refine ⟨1409911073270401699372349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939940715513601132914899 1409911073270401699372349)
                    ·
                      refine ⟨528716652476400637264631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1409911073270401699372349 528716652476400637264631)
                      ·
                        rfl

theorem cell23_1029672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1029672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029672 prefixEnd_1029672 := by exact prefixLift 1029672
  have htrace : WordTrace (prefixWord ++ tailWord_1029672) baseStart_1029672 baseEnd_1029672 := by
    simpa [prefixWord, tailWord_1029672, baseEnd_1029672] using wordTrace_append hprefix tailTrace_1029672
  have hstable : (prefixWord ++ tailWord_1029672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029672).length < 2 ^ (prefixWord ++ tailWord_1029672).sum := by decide
  have hdescent : baseEnd_1029672 < baseStart_1029672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029681 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1029681 : Nat := 118140960795 + 1029681 * 2 ^ 59
def prefixEnd_1029681 : Nat := 4983230072969 + 3 ^ 40 * 1029681 * 2
def baseEnd_1029681 : Nat := 528721273802291102052089

theorem tailTrace_1029681 : CollatzResearch.WordTrace tailWord_1029681 prefixEnd_1029681 528721273802291102052089 := by
  unfold tailWord_1029681
  simp only [CollatzResearch.WordTrace]
  refine ⟨37555551382649067359336897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25037034255099378239557931 37555551382649067359336897)
  ·
    refine ⟨28166663536986800519502673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37555551382649067359336897 28166663536986800519502673)
    ·
      refine ⟨21124997652740100389627005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28166663536986800519502673 21124997652740100389627005)
      ·
        refine ⟨7921874119777537646110127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21124997652740100389627005 7921874119777537646110127)
        ·
          refine ⟨11882811179666306469165191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7921874119777537646110127 11882811179666306469165191)
          ·
            refine ⟨17824216769499459703747787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882811179666306469165191 17824216769499459703747787)
            ·
              refine ⟨26736325154249189555621681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824216769499459703747787 26736325154249189555621681)
              ·
                refine ⟨20052243865686892166716261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26736325154249189555621681 20052243865686892166716261)
                ·
                  refine ⟨3759795724816292281259299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20052243865686892166716261 3759795724816292281259299)
                  ·
                    refine ⟨5639693587224438421888949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759795724816292281259299 5639693587224438421888949)
                    ·
                      refine ⟨528721273802291102052089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5639693587224438421888949 528721273802291102052089)
                      ·
                        rfl

theorem cell23_1029681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1029681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029681 prefixEnd_1029681 := by exact prefixLift 1029681
  have htrace : WordTrace (prefixWord ++ tailWord_1029681) baseStart_1029681 baseEnd_1029681 := by
    simpa [prefixWord, tailWord_1029681, baseEnd_1029681] using wordTrace_append hprefix tailTrace_1029681
  have hstable : (prefixWord ++ tailWord_1029681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029681).length < 2 ^ (prefixWord ++ tailWord_1029681).sum := by decide
  have hdescent : baseEnd_1029681 < baseStart_1029681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029695 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 4, 2]
def baseStart_1029695 : Nat := 118140960795 + 1029695 * 2 ^ 59
def prefixEnd_1029695 : Nat := 4983230072969 + 3 ^ 40 * 1029695 * 2
def baseEnd_1029695 : Nat := 528728462531454047277025

theorem tailTrace_1029695 : CollatzResearch.WordTrace tailWord_1029695 prefixEnd_1029695 528728462531454047277025 := by
  unfold tailWord_1029695
  simp only [CollatzResearch.WordTrace]
  refine ⟨37556062004598347750346539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25037374669732231833564359 37556062004598347750346539)
  ·
    refine ⟨56334093006897521625519809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37556062004598347750346539 56334093006897521625519809)
    ·
      refine ⟨42250569755173141219139857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56334093006897521625519809 42250569755173141219139857)
      ·
        refine ⟨31687927316379855914354893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42250569755173141219139857 31687927316379855914354893)
        ·
          refine ⟨11882972743642445967883085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31687927316379855914354893 11882972743642445967883085)
          ·
            refine ⟨4456114778865917237956157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11882972743642445967883085 4456114778865917237956157)
            ·
              refine ⟨1671043042074718964233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4456114778865917237956157 1671043042074718964233559)
              ·
                refine ⟨2506564563112078446350339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671043042074718964233559 2506564563112078446350339)
                ·
                  refine ⟨3759846844668117669525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506564563112078446350339 3759846844668117669525509)
                  ·
                    refine ⟨704971283375272063036033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759846844668117669525509 704971283375272063036033)
                    ·
                      refine ⟨528728462531454047277025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 704971283375272063036033 528728462531454047277025)
                      ·
                        rfl

theorem cell23_1029695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_1029695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029695 prefixEnd_1029695 := by exact prefixLift 1029695
  have htrace : WordTrace (prefixWord ++ tailWord_1029695) baseStart_1029695 baseEnd_1029695 := by
    simpa [prefixWord, tailWord_1029695, baseEnd_1029695] using wordTrace_append hprefix tailTrace_1029695
  have hstable : (prefixWord ++ tailWord_1029695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029695).length < 2 ^ (prefixWord ++ tailWord_1029695).sum := by decide
  have hdescent : baseEnd_1029695 < baseStart_1029695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029701 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 7]
def baseStart_1029701 : Nat := 118140960795 + 1029701 * 2 ^ 59
def prefixEnd_1029701 : Nat := 4983230072969 + 3 ^ 40 * 1029701 * 2
def baseEnd_1029701 : Nat := 58747949268375669311333

theorem tailTrace_1029701 : CollatzResearch.WordTrace tailWord_1029701 prefixEnd_1029701 58747949268375669311333 := by
  unfold tailWord_1029701
  simp only [CollatzResearch.WordTrace]
  refine ⟨37556280842576610775064957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25037520561717740516709971 37556280842576610775064957)
  ·
    refine ⟨14083605315966229040649359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37556280842576610775064957 14083605315966229040649359)
    ·
      refine ⟨21125407973949343560974039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14083605315966229040649359 21125407973949343560974039)
      ·
        refine ⟨31688111960924015341461059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21125407973949343560974039 31688111960924015341461059)
        ·
          refine ⟨47532167941386023012191589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31688111960924015341461059 47532167941386023012191589)
          ·
            refine ⟨8912281489009879314785923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47532167941386023012191589 8912281489009879314785923)
            ·
              refine ⟨13368422233514818972178885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912281489009879314785923 13368422233514818972178885)
              ·
                refine ⟨2506579168784028557283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13368422233514818972178885 2506579168784028557283541)
                ·
                  refine ⟨58747949268375669311333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2506579168784028557283541 58747949268375669311333)
                  ·
                    rfl

theorem cell23_1029701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_1029701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029701 prefixEnd_1029701 := by exact prefixLift 1029701
  have htrace : WordTrace (prefixWord ++ tailWord_1029701) baseStart_1029701 baseEnd_1029701 := by
    simpa [prefixWord, tailWord_1029701, baseEnd_1029701] using wordTrace_append hprefix tailTrace_1029701
  have hstable : (prefixWord ++ tailWord_1029701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029701).length < 2 ^ (prefixWord ++ tailWord_1029701).sum := by decide
  have hdescent : baseEnd_1029701 < baseStart_1029701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029746 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1029746 : Nat := 118140960795 + 1029746 * 2 ^ 59
def prefixEnd_1029746 : Nat := 4983230072969 + 3 ^ 40 * 1029746 * 2
def baseEnd_1029746 : Nat := 528754650044833347739291

theorem tailTrace_1029746 : CollatzResearch.WordTrace tailWord_1029746 prefixEnd_1029746 528754650044833347739291 := by
  unfold tailWord_1029746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389480531853395865113273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25038614751609055640302061 9389480531853395865113273)
  ·
    refine ⟨7042110398890046898834955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9389480531853395865113273 7042110398890046898834955)
    ·
      refine ⟨10563165598335070348252433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042110398890046898834955 10563165598335070348252433)
      ·
        refine ⟨7922374198751302761189325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10563165598335070348252433 7922374198751302761189325)
        ·
          refine ⟨2970890324531738535445997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7922374198751302761189325 2970890324531738535445997)
          ·
            refine ⟨1114083871699401950792249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2970890324531738535445997 1114083871699401950792249)
            ·
              refine ⟨835562903774551463094187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114083871699401950792249 835562903774551463094187)
              ·
                refine ⟨1253344355661827194641281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835562903774551463094187 1253344355661827194641281)
                ·
                  refine ⟨940008266746370395980961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253344355661827194641281 940008266746370395980961)
                  ·
                    refine ⟨705006200059777796985721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 940008266746370395980961 705006200059777796985721)
                    ·
                      refine ⟨528754650044833347739291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705006200059777796985721 528754650044833347739291)
                      ·
                        rfl

theorem cell23_1029746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1029746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029746 prefixEnd_1029746 := by exact prefixLift 1029746
  have htrace : WordTrace (prefixWord ++ tailWord_1029746) baseStart_1029746 baseEnd_1029746 := by
    simpa [prefixWord, tailWord_1029746, baseEnd_1029746] using wordTrace_append hprefix tailTrace_1029746
  have hstable : (prefixWord ++ tailWord_1029746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029746).length < 2 ^ (prefixWord ++ tailWord_1029746).sum := by decide
  have hdescent : baseEnd_1029746 < baseStart_1029746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029801 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_1029801 : Nat := 118140960795 + 1029801 * 2 ^ 59
def prefixEnd_1029801 : Nat := 4983230072969 + 3 ^ 40 * 1029801 * 2
def baseEnd_1029801 : Nat := 528782891480830632551537

theorem tailTrace_1029801 : CollatzResearch.WordTrace tailWord_1029801 prefixEnd_1029801 528782891480830632551537 := by
  unfold tailWord_1029801
  simp only [CollatzResearch.WordTrace]
  refine ⟨37559928142214327853705257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25039952094809551902470171 37559928142214327853705257)
  ·
    refine ⟨28169946106660745890278943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37559928142214327853705257 28169946106660745890278943)
    ·
      refine ⟨42254919159991118835418415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169946106660745890278943 42254919159991118835418415)
      ·
        refine ⟨63382378739986678253127623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42254919159991118835418415 63382378739986678253127623)
        ·
          refine ⟨95073568109980017379691435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63382378739986678253127623 95073568109980017379691435)
          ·
            refine ⟨142610352164970026069537153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95073568109980017379691435 142610352164970026069537153)
            ·
              refine ⟨106957764123727519552152865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142610352164970026069537153 106957764123727519552152865)
              ·
                refine ⟨80218323092795639664114649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106957764123727519552152865 80218323092795639664114649)
                ·
                  refine ⟨60163742319596729748085987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80218323092795639664114649 60163742319596729748085987)
                  ·
                    refine ⟨90245613479395094622128981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60163742319596729748085987 90245613479395094622128981)
                    ·
                      refine ⟨528782891480830632551537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 90245613479395094622128981 528782891480830632551537)
                      ·
                        rfl

theorem cell23_1029801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_1029801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029801 prefixEnd_1029801 := by exact prefixLift 1029801
  have htrace : WordTrace (prefixWord ++ tailWord_1029801) baseStart_1029801 baseEnd_1029801 := by
    simpa [prefixWord, tailWord_1029801, baseEnd_1029801] using wordTrace_append hprefix tailTrace_1029801
  have hstable : (prefixWord ++ tailWord_1029801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029801).length < 2 ^ (prefixWord ++ tailWord_1029801).sum := by decide
  have hdescent : baseEnd_1029801 < baseStart_1029801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029805 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1029805 : Nat := 118140960795 + 1029805 * 2 ^ 59
def prefixEnd_1029805 : Nat := 4983230072969 + 3 ^ 40 * 1029805 * 2
def baseEnd_1029805 : Nat := 528784945403448616901519

theorem tailTrace_1029805 : CollatzResearch.WordTrace tailWord_1029805 prefixEnd_1029805 528784945403448616901519 := by
  unfold tailWord_1029805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560074034199836536850869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040049356133224357900579 37560074034199836536850869)
  ·
    refine ⟨3521256940706234675329769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37560074034199836536850869 3521256940706234675329769)
    ·
      refine ⟨2640942705529676006497327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521256940706234675329769 2640942705529676006497327)
      ·
        refine ⟨3961414058294514009745991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640942705529676006497327 3961414058294514009745991)
        ·
          refine ⟨5942121087441771014618987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961414058294514009745991 5942121087441771014618987)
          ·
            refine ⟨8913181631162656521928481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942121087441771014618987 8913181631162656521928481)
            ·
              refine ⟨6684886223371992391446361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8913181631162656521928481 6684886223371992391446361)
              ·
                refine ⟨5013664667528994293584771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684886223371992391446361 5013664667528994293584771)
                ·
                  refine ⟨7520497001293491440377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013664667528994293584771 7520497001293491440377157)
                  ·
                    refine ⟨1410093187742529645070717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520497001293491440377157 1410093187742529645070717)
                    ·
                      refine ⟨528784945403448616901519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410093187742529645070717 528784945403448616901519)
                      ·
                        rfl

theorem cell23_1029805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1029805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029805 prefixEnd_1029805 := by exact prefixLift 1029805
  have htrace : WordTrace (prefixWord ++ tailWord_1029805) baseStart_1029805 baseEnd_1029805 := by
    simpa [prefixWord, tailWord_1029805, baseEnd_1029805] using wordTrace_append hprefix tailTrace_1029805
  have hstable : (prefixWord ++ tailWord_1029805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029805).length < 2 ^ (prefixWord ++ tailWord_1029805).sum := by decide
  have hdescent : baseEnd_1029805 < baseStart_1029805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029808 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 6]
def baseStart_1029808 : Nat := 118140960795 + 1029808 * 2 ^ 59
def prefixEnd_1029808 : Nat := 4983230072969 + 3 ^ 40 * 1029808 * 2
def baseEnd_1029808 : Nat := 58754053982823567240445

theorem tailTrace_1029808 : CollatzResearch.WordTrace tailWord_1029808 prefixEnd_1029808 58754053982823567240445 := by
  unfold tailWord_1029808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18780091726594484024605039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25040122302125978699473385 18780091726594484024605039)
  ·
    refine ⟨28170137589891726036907559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18780091726594484024605039 28170137589891726036907559)
    ·
      refine ⟨42255206384837589055361339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28170137589891726036907559 42255206384837589055361339)
      ·
        refine ⟨63382809577256383583042009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255206384837589055361339 63382809577256383583042009)
        ·
          refine ⟨47537107182942287687281507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63382809577256383583042009 47537107182942287687281507)
          ·
            refine ⟨71305660774413431530922261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47537107182942287687281507 71305660774413431530922261)
            ·
              refine ⟨3342452848800629603011981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71305660774413431530922261 3342452848800629603011981)
              ·
                refine ⟨1253419818300236101129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342452848800629603011981 1253419818300236101129493)
                ·
                  refine ⟨58754053982823567240445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253419818300236101129493 58754053982823567240445)
                  ·
                    rfl

theorem cell23_1029808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_1029808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029808 prefixEnd_1029808 := by exact prefixLift 1029808
  have htrace : WordTrace (prefixWord ++ tailWord_1029808) baseStart_1029808 baseEnd_1029808 := by
    simpa [prefixWord, tailWord_1029808, baseEnd_1029808] using wordTrace_append hprefix tailTrace_1029808
  have hstable : (prefixWord ++ tailWord_1029808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029808).length < 2 ^ (prefixWord ++ tailWord_1029808).sum := by decide
  have hdescent : baseEnd_1029808 < baseStart_1029808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029822 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1029822 : Nat := 118140960795 + 1029822 * 2 ^ 59
def prefixEnd_1029822 : Nat := 4983230072969 + 3 ^ 40 * 1029822 * 2
def baseEnd_1029822 : Nat := 528793674574575050388941

theorem tailTrace_1029822 : CollatzResearch.WordTrace tailWord_1029822 prefixEnd_1029822 528793674574575050388941 := by
  unfold tailWord_1029822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695086759392281055027465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25040462716758832293479813 4695086759392281055027465)
  ·
    refine ⟨3521315069544210791270599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4695086759392281055027465 3521315069544210791270599)
    ·
      refine ⟨5281972604316316186905899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521315069544210791270599 5281972604316316186905899)
      ·
        refine ⟨7922958906474474280358849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281972604316316186905899 7922958906474474280358849)
        ·
          refine ⟨5942219179855855710269137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7922958906474474280358849 5942219179855855710269137)
          ·
            refine ⟨4456664384891891782701853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5942219179855855710269137 4456664384891891782701853)
            ·
              refine ⟨1671249144334459418513195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4456664384891891782701853 1671249144334459418513195)
              ·
                refine ⟨2506873716501689127769793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671249144334459418513195 2506873716501689127769793)
                ·
                  refine ⟨1880155287376266845827345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506873716501689127769793 1880155287376266845827345)
                  ·
                    refine ⟨1410116465532200134370509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880155287376266845827345 1410116465532200134370509)
                    ·
                      refine ⟨528793674574575050388941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410116465532200134370509 528793674574575050388941)
                      ·
                        rfl

theorem cell23_1029822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1029822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029822 prefixEnd_1029822 := by exact prefixLift 1029822
  have htrace : WordTrace (prefixWord ++ tailWord_1029822) baseStart_1029822 baseEnd_1029822 := by
    simpa [prefixWord, tailWord_1029822, baseEnd_1029822] using wordTrace_append hprefix tailTrace_1029822
  have hstable : (prefixWord ++ tailWord_1029822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029822).length < 2 ^ (prefixWord ++ tailWord_1029822).sum := by decide
  have hdescent : baseEnd_1029822 < baseStart_1029822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029842 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_1029842 : Nat := 118140960795 + 1029842 * 2 ^ 59
def prefixEnd_1029842 : Nat := 4983230072969 + 3 ^ 40 * 1029842 * 2
def baseEnd_1029842 : Nat := 58755993798629441348761

theorem tailTrace_1029842 : CollatzResearch.WordTrace tailWord_1029842 prefixEnd_1029842 58755993798629441348761 := by
  unfold tailWord_1029842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390355883766447963986945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25040949023377194570631853 9390355883766447963986945)
  ·
    refine ⟨7042766912824835972990209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9390355883766447963986945 7042766912824835972990209)
    ·
      refine ⟨5282075184618626979742657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7042766912824835972990209 5282075184618626979742657)
      ·
        refine ⟨3961556388463970234806993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5282075184618626979742657 3961556388463970234806993)
        ·
          refine ⟨2971167291347977676105245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3961556388463970234806993 2971167291347977676105245)
          ·
            refine ⟨1114187734255491628539467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2971167291347977676105245 1114187734255491628539467)
            ·
              refine ⟨1671281601383237442809201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114187734255491628539467 1671281601383237442809201)
              ·
                refine ⟨1253461201037428082106901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671281601383237442809201 1253461201037428082106901)
                ·
                  refine ⟨58755993798629441348761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253461201037428082106901 58755993798629441348761)
                  ·
                    rfl

theorem cell23_1029842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_1029842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029842 prefixEnd_1029842 := by exact prefixLift 1029842
  have htrace : WordTrace (prefixWord ++ tailWord_1029842) baseStart_1029842 baseEnd_1029842 := by
    simpa [prefixWord, tailWord_1029842, baseEnd_1029842] using wordTrace_append hprefix tailTrace_1029842
  have hstable : (prefixWord ++ tailWord_1029842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029842).length < 2 ^ (prefixWord ++ tailWord_1029842).sum := by decide
  have hdescent : baseEnd_1029842 < baseStart_1029842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029846 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1029846 : Nat := 118140960795 + 1029846 * 2 ^ 59
def prefixEnd_1029846 : Nat := 4983230072969 + 3 ^ 40 * 1029846 * 2
def baseEnd_1029846 : Nat := 176268666036760985496277

theorem tailTrace_1029846 : CollatzResearch.WordTrace tailWord_1029846 prefixEnd_1029846 176268666036760985496277 := by
  unfold tailWord_1029846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347598089190706283693337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25041046284700867026062261 2347598089190706283693337)
  ·
    refine ⟨1760698566893029712770003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2347598089190706283693337 1760698566893029712770003)
    ·
      refine ⟨2641047850339544569155005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760698566893029712770003 2641047850339544569155005)
      ·
        refine ⟨990392943877329213433127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641047850339544569155005 990392943877329213433127)
        ·
          refine ⟨1485589415815993820149691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990392943877329213433127 1485589415815993820149691)
          ·
            refine ⟨2228384123723990730224537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485589415815993820149691 2228384123723990730224537)
            ·
              refine ⟨1671288092792993047668403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228384123723990730224537 1671288092792993047668403)
              ·
                refine ⟨2506932139189489571502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671288092792993047668403 2506932139189489571502605)
                ·
                  refine ⟨940099552196058589313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2506932139189489571502605 940099552196058589313477)
                  ·
                    refine ⟨176268666036760985496277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 940099552196058589313477 176268666036760985496277)
                    ·
                      rfl

theorem cell23_1029846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1029846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029846 prefixEnd_1029846 := by exact prefixLift 1029846
  have htrace : WordTrace (prefixWord ++ tailWord_1029846) baseStart_1029846 baseEnd_1029846 := by
    simpa [prefixWord, tailWord_1029846, baseEnd_1029846] using wordTrace_append hprefix tailTrace_1029846
  have hstable : (prefixWord ++ tailWord_1029846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029846).length < 2 ^ (prefixWord ++ tailWord_1029846).sum := by decide
  have hdescent : baseEnd_1029846 < baseStart_1029846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029875 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 4]
def baseStart_1029875 : Nat := 118140960795 + 1029875 * 2 ^ 59
def prefixEnd_1029875 : Nat := 4983230072969 + 3 ^ 40 * 1029875 * 2
def baseEnd_1029875 : Nat := 528820889049263343026197

theorem tailTrace_1029875 : CollatzResearch.WordTrace tailWord_1029875 prefixEnd_1029875 528820889049263343026197 := by
  unfold tailWord_1029875
  simp only [CollatzResearch.WordTrace]
  refine ⟨37562627143946238491899079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25041751429297492327932719 37562627143946238491899079)
  ·
    refine ⟨56343940715919357737848619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37562627143946238491899079 56343940715919357737848619)
    ·
      refine ⟨84515911073879036606772929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56343940715919357737848619 84515911073879036606772929)
      ·
        refine ⟨63386933305409277455079697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84515911073879036606772929 63386933305409277455079697)
        ·
          refine ⟨47540199979056958091309773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63386933305409277455079697 47540199979056958091309773)
          ·
            refine ⟨17827574992146359284241165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47540199979056958091309773 17827574992146359284241165)
            ·
              refine ⟨6685340622054884731590437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17827574992146359284241165 6685340622054884731590437)
              ·
                refine ⟨1253501366635290887173207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6685340622054884731590437 1253501366635290887173207)
                ·
                  refine ⟨1880252049952936330759811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253501366635290887173207 1880252049952936330759811)
                  ·
                    refine ⟨2820378074929404496139717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880252049952936330759811 2820378074929404496139717)
                    ·
                      refine ⟨528820889049263343026197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2820378074929404496139717 528820889049263343026197)
                      ·
                        rfl

theorem cell23_1029875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_1029875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029875 prefixEnd_1029875 := by exact prefixLift 1029875
  have htrace : WordTrace (prefixWord ++ tailWord_1029875) baseStart_1029875 baseEnd_1029875 := by
    simpa [prefixWord, tailWord_1029875, baseEnd_1029875] using wordTrace_append hprefix tailTrace_1029875
  have hstable : (prefixWord ++ tailWord_1029875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029875).length < 2 ^ (prefixWord ++ tailWord_1029875).sum := by decide
  have hdescent : baseEnd_1029875 < baseStart_1029875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029892 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1029892 : Nat := 118140960795 + 1029892 * 2 ^ 59
def prefixEnd_1029892 : Nat := 4983230072969 + 3 ^ 40 * 1029892 * 2
def baseEnd_1029892 : Nat := 528829618220389776513619

theorem tailTrace_1029892 : CollatzResearch.WordTrace tailWord_1029892 prefixEnd_1029892 528829618220389776513619 := by
  unfold tailWord_1029892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18781623592442325197633965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25042164789923100263511953 18781623592442325197633965)
  ·
    refine ⟨7043108847165871949112737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18781623592442325197633965 7043108847165871949112737)
    ·
      refine ⟨5282331635374403961834553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7043108847165871949112737 5282331635374403961834553)
      ·
        refine ⟨3961748726530802971375915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5282331635374403961834553 3961748726530802971375915)
        ·
          refine ⟨5942623089796204457063873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961748726530802971375915 5942623089796204457063873)
          ·
            refine ⟨4456967317347153342797905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5942623089796204457063873 4456967317347153342797905)
            ·
              refine ⟨3342725488010365007098429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456967317347153342797905 3342725488010365007098429)
              ·
                refine ⟨1253522058003886877661911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342725488010365007098429 1253522058003886877661911)
                ·
                  refine ⟨1880283087005830316492867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253522058003886877661911 1880283087005830316492867)
                  ·
                    refine ⟨2820424630508745474739301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880283087005830316492867 2820424630508745474739301)
                    ·
                      refine ⟨528829618220389776513619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2820424630508745474739301 528829618220389776513619)
                      ·
                        rfl

theorem cell23_1029892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1029892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029892 prefixEnd_1029892 := by exact prefixLift 1029892
  have htrace : WordTrace (prefixWord ++ tailWord_1029892) baseStart_1029892 baseEnd_1029892 := by
    simpa [prefixWord, tailWord_1029892, baseEnd_1029892] using wordTrace_append hprefix tailTrace_1029892
  have hstable : (prefixWord ++ tailWord_1029892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029892).length < 2 ^ (prefixWord ++ tailWord_1029892).sum := by decide
  have hdescent : baseEnd_1029892 < baseStart_1029892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029898 : List Nat := [3, 1, 2, 2, 1, 3, 11]
def baseStart_1029898 : Nat := 118140960795 + 1029898 * 2 ^ 59
def prefixEnd_1029898 : Nat := 4983230072969 + 3 ^ 40 * 1029898 * 2
def baseEnd_1029898 : Nat := 6528798754374280901711

theorem tailTrace_1029898 : CollatzResearch.WordTrace tailWord_1029898 prefixEnd_1029898 6528798754374280901711 := by
  unfold tailWord_1029898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390866505715728354996587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25042310681908608946657565 9390866505715728354996587)
  ·
    refine ⟨14086299758573592532494881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9390866505715728354996587 14086299758573592532494881)
    ·
      refine ⟨10564724818930194399371161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14086299758573592532494881 10564724818930194399371161)
      ·
        refine ⟨7923543614197645799528371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10564724818930194399371161 7923543614197645799528371)
        ·
          refine ⟨11885315421296468699292557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7923543614197645799528371 11885315421296468699292557)
          ·
            refine ⟨4456993282986175762234709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11885315421296468699292557 4456993282986175762234709)
            ·
              refine ⟨6528798754374280901711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4456993282986175762234709 6528798754374280901711)
              ·
                rfl

theorem cell23_1029898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 11].length) (baseStart_1029898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029898 prefixEnd_1029898 := by exact prefixLift 1029898
  have htrace : WordTrace (prefixWord ++ tailWord_1029898) baseStart_1029898 baseEnd_1029898 := by
    simpa [prefixWord, tailWord_1029898, baseEnd_1029898] using wordTrace_append hprefix tailTrace_1029898
  have hstable : (prefixWord ++ tailWord_1029898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029898).length < 2 ^ (prefixWord ++ tailWord_1029898).sum := by decide
  have hdescent : baseEnd_1029898 < baseStart_1029898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029909 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_1029909 : Nat := 118140960795 + 1029909 * 2 ^ 59
def prefixEnd_1029909 : Nat := 4983230072969 + 3 ^ 40 * 1029909 * 2
def baseEnd_1029909 : Nat := 528838347391516210001041

theorem tailTrace_1029909 : CollatzResearch.WordTrace tailWord_1029909 prefixEnd_1029909 528838347391516210001041 := by
  unfold tailWord_1029909
  simp only [CollatzResearch.WordTrace]
  refine ⟨37563867225823062298636781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25042578150548708199091187 37563867225823062298636781)
  ·
    refine ⟨14086450209683648361988793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37563867225823062298636781 14086450209683648361988793)
    ·
      refine ⟨10564837657262736271491595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14086450209683648361988793 10564837657262736271491595)
      ·
        refine ⟨15847256485894104407237393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10564837657262736271491595 15847256485894104407237393)
        ·
          refine ⟨11885442364420578305428045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15847256485894104407237393 11885442364420578305428045)
          ·
            refine ⟨4457040886657716864535517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11885442364420578305428045 4457040886657716864535517)
            ·
              refine ⟨1671390332496643824200819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4457040886657716864535517 1671390332496643824200819)
              ·
                refine ⟨2507085498744965736301229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671390332496643824200819 2507085498744965736301229)
                ·
                  refine ⟨940157062029362151112961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2507085498744965736301229 940157062029362151112961)
                  ·
                    refine ⟨705117796522021613334721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 940157062029362151112961 705117796522021613334721)
                    ·
                      refine ⟨528838347391516210001041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705117796522021613334721 528838347391516210001041)
                      ·
                        rfl

theorem cell23_1029909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_1029909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029909 prefixEnd_1029909 := by exact prefixLift 1029909
  have htrace : WordTrace (prefixWord ++ tailWord_1029909) baseStart_1029909 baseEnd_1029909 := by
    simpa [prefixWord, tailWord_1029909, baseEnd_1029909] using wordTrace_append hprefix tailTrace_1029909
  have hstable : (prefixWord ++ tailWord_1029909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029909).length < 2 ^ (prefixWord ++ tailWord_1029909).sum := by decide
  have hdescent : baseEnd_1029909 < baseStart_1029909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029935 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 7, 2]
def baseStart_1029935 : Nat := 118140960795 + 1029935 * 2 ^ 59
def prefixEnd_1029935 : Nat := 4983230072969 + 3 ^ 40 * 1029935 * 2
def baseEnd_1029935 : Nat := 528851697888533108275921

theorem tailTrace_1029935 : CollatzResearch.WordTrace tailWord_1029935 prefixEnd_1029935 528851697888533108275921 := by
  unfold tailWord_1029935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37564815523728868739083259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25043210349152579159388839 37564815523728868739083259)
  ·
    refine ⟨56347223285593303108624889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37564815523728868739083259 56347223285593303108624889)
    ·
      refine ⟨42260417464194977331468667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56347223285593303108624889 42260417464194977331468667)
      ·
        refine ⟨63390626196292465997203001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42260417464194977331468667 63390626196292465997203001)
        ·
          refine ⟨47542969647219349497902251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63390626196292465997203001 47542969647219349497902251)
          ·
            refine ⟨71314454470829024246853377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47542969647219349497902251 71314454470829024246853377)
            ·
              refine ⟨53485840853121768185140033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71314454470829024246853377 53485840853121768185140033)
              ·
                refine ⟨40114380639841326138855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53485840853121768185140033 40114380639841326138855025)
                ·
                  refine ⟨30085785479880994604141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40114380639841326138855025 30085785479880994604141269)
                  ·
                    refine ⟨705135597184710811034561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30085785479880994604141269 705135597184710811034561)
                    ·
                      refine ⟨528851697888533108275921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705135597184710811034561 528851697888533108275921)
                      ·
                        rfl

theorem cell23_1029935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7, 2].length) (baseStart_1029935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029935 prefixEnd_1029935 := by exact prefixLift 1029935
  have htrace : WordTrace (prefixWord ++ tailWord_1029935) baseStart_1029935 baseEnd_1029935 := by
    simpa [prefixWord, tailWord_1029935, baseEnd_1029935] using wordTrace_append hprefix tailTrace_1029935
  have hstable : (prefixWord ++ tailWord_1029935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029935).length < 2 ^ (prefixWord ++ tailWord_1029935).sum := by decide
  have hdescent : baseEnd_1029935 < baseStart_1029935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029985 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1029985 : Nat := 118140960795 + 1029985 * 2 ^ 59
def prefixEnd_1029985 : Nat := 4983230072969 + 3 ^ 40 * 1029985 * 2
def baseEnd_1029985 : Nat := 528877371921257912650691

theorem tailTrace_1029985 : CollatzResearch.WordTrace tailWord_1029985 prefixEnd_1029985 528877371921257912650691 := by
  unfold tailWord_1029985
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566639173547727278403409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25044426115698484852268939 37566639173547727278403409)
  ·
    refine ⟨28174979380160795458802557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37566639173547727278403409 28174979380160795458802557)
    ·
      refine ⟨10565617267560298297050959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28174979380160795458802557 10565617267560298297050959)
      ·
        refine ⟨15848425901340447445576439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10565617267560298297050959 15848425901340447445576439)
        ·
          refine ⟨23772638852010671168364659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15848425901340447445576439 23772638852010671168364659)
          ·
            refine ⟨35658958278016006752546989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772638852010671168364659 35658958278016006752546989)
            ·
              refine ⟨13372109354256002532205121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35658958278016006752546989 13372109354256002532205121)
              ·
                refine ⟨10029082015692001899153841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372109354256002532205121 10029082015692001899153841)
                ·
                  refine ⟨7521811511769001424365381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029082015692001899153841 7521811511769001424365381)
                  ·
                    refine ⟨1410339658456687767068509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521811511769001424365381 1410339658456687767068509)
                    ·
                      refine ⟨528877371921257912650691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410339658456687767068509 528877371921257912650691)
                      ·
                        rfl

theorem cell23_1029985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1029985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1029985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1029985 prefixEnd_1029985 := by exact prefixLift 1029985
  have htrace : WordTrace (prefixWord ++ tailWord_1029985) baseStart_1029985 baseEnd_1029985 := by
    simpa [prefixWord, tailWord_1029985, baseEnd_1029985] using wordTrace_append hprefix tailTrace_1029985
  have hstable : (prefixWord ++ tailWord_1029985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029985).length < 2 ^ (prefixWord ++ tailWord_1029985).sum := by decide
  have hdescent : baseEnd_1029985 < baseStart_1029985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030005 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 9]
def baseStart_1030005 : Nat := 118140960795 + 1030005 * 2 ^ 59
def prefixEnd_1030005 : Nat := 4983230072969 + 3 ^ 40 * 1030005 * 2
def baseEnd_1030005 : Nat := 58765293503816426044511

theorem tailTrace_1030005 : CollatzResearch.WordTrace tailWord_1030005 prefixEnd_1030005 58765293503816426044511 := by
  unfold tailWord_1030005
  simp only [CollatzResearch.WordTrace]
  refine ⟨37567368633475270694131469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25044912422316847129420979 37567368633475270694131469)
  ·
    refine ⟨14087763237553226510299301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37567368633475270694131469 14087763237553226510299301)
    ·
      refine ⟨2641455607041229970681119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14087763237553226510299301 2641455607041229970681119)
      ·
        refine ⟨3962183410561844956021679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641455607041229970681119 3962183410561844956021679)
        ·
          refine ⟨5943275115842767434032519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962183410561844956021679 5943275115842767434032519)
          ·
            refine ⟨8914912673764151151048779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943275115842767434032519 8914912673764151151048779)
            ·
              refine ⟨13372369010646226726573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914912673764151151048779 13372369010646226726573169)
              ·
                refine ⟨10029276757984670044929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372369010646226726573169 10029276757984670044929877)
                ·
                  refine ⟨58765293503816426044511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10029276757984670044929877 58765293503816426044511)
                  ·
                    rfl

theorem cell23_1030005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_1030005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030005 prefixEnd_1030005 := by exact prefixLift 1030005
  have htrace : WordTrace (prefixWord ++ tailWord_1030005) baseStart_1030005 baseEnd_1030005 := by
    simpa [prefixWord, tailWord_1030005, baseEnd_1030005] using wordTrace_append hprefix tailTrace_1030005
  have hstable : (prefixWord ++ tailWord_1030005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030005).length < 2 ^ (prefixWord ++ tailWord_1030005).sum := by decide
  have hdescent : baseEnd_1030005 < baseStart_1030005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030072 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1030072 : Nat := 118140960795 + 1030072 * 2 ^ 59
def prefixEnd_1030072 : Nat := 4983230072969 + 3 ^ 40 * 1030072 * 2
def baseEnd_1030072 : Nat := 528922044738199072262791

theorem tailTrace_1030072 : CollatzResearch.WordTrace tailWord_1030072 prefixEnd_1030072 528922044738199072262791 := by
  unfold tailWord_1030072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784906162116270568410235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25046541549488360757880313 18784906162116270568410235)
  ·
    refine ⟨28177359243174405852615353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18784906162116270568410235 28177359243174405852615353)
    ·
      refine ⟨21133019432380804389461515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28177359243174405852615353 21133019432380804389461515)
      ·
        refine ⟨31699529148571206584192273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21133019432380804389461515 31699529148571206584192273)
        ·
          refine ⟨23774646861428404938144205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31699529148571206584192273 23774646861428404938144205)
          ·
            refine ⟨8915492573035651851804077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23774646861428404938144205 8915492573035651851804077)
            ·
              refine ⟨3343309714888369444426529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8915492573035651851804077 3343309714888369444426529)
              ·
                refine ⟨2507482286166277083319897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343309714888369444426529 2507482286166277083319897)
                ·
                  refine ⟨1880611714624707812489923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507482286166277083319897 1880611714624707812489923)
                  ·
                    refine ⟨2820917571937061718734885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880611714624707812489923 2820917571937061718734885)
                    ·
                      refine ⟨528922044738199072262791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2820917571937061718734885 528922044738199072262791)
                      ·
                        rfl

theorem cell23_1030072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1030072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030072 prefixEnd_1030072 := by exact prefixLift 1030072
  have htrace : WordTrace (prefixWord ++ tailWord_1030072) baseStart_1030072 baseEnd_1030072 := by
    simpa [prefixWord, tailWord_1030072, baseEnd_1030072] using wordTrace_append hprefix tailTrace_1030072
  have hstable : (prefixWord ++ tailWord_1030072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030072).length < 2 ^ (prefixWord ++ tailWord_1030072).sum := by decide
  have hdescent : baseEnd_1030072 < baseStart_1030072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030085 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_1030085 : Nat := 118140960795 + 1030085 * 2 ^ 59
def prefixEnd_1030085 : Nat := 4983230072969 + 3 ^ 40 * 1030085 * 2
def baseEnd_1030085 : Nat := 528928719986707521400231

theorem tailTrace_1030085 : CollatzResearch.WordTrace tailWord_1030085 prefixEnd_1030085 528928719986707521400231 := by
  unfold tailWord_1030085
  simp only [CollatzResearch.WordTrace]
  refine ⟨37570286473185444357043709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25046857648790296238029139 37570286473185444357043709)
  ·
    refine ⟨14088857427444541633891391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37570286473185444357043709 14088857427444541633891391)
    ·
      refine ⟨21133286141166812450837087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14088857427444541633891391 21133286141166812450837087)
      ·
        refine ⟨31699929211750218676255631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21133286141166812450837087 31699929211750218676255631)
        ·
          refine ⟨47549893817625328014383447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31699929211750218676255631 47549893817625328014383447)
          ·
            refine ⟨71324840726437992021575171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47549893817625328014383447 71324840726437992021575171)
            ·
              refine ⟨106987261089656988032362757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71324840726437992021575171 106987261089656988032362757)
              ·
                refine ⟨20060111454310685256068017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106987261089656988032362757 20060111454310685256068017)
                ·
                  refine ⟨15045083590733013942051013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20060111454310685256068017 15045083590733013942051013)
                  ·
                    refine ⟨2820953173262440114134565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15045083590733013942051013 2820953173262440114134565)
                    ·
                      refine ⟨528928719986707521400231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2820953173262440114134565 528928719986707521400231)
                      ·
                        rfl

theorem cell23_1030085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_1030085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030085 prefixEnd_1030085 := by exact prefixLift 1030085
  have htrace : WordTrace (prefixWord ++ tailWord_1030085) baseStart_1030085 baseEnd_1030085 := by
    simpa [prefixWord, tailWord_1030085, baseEnd_1030085] using wordTrace_append hprefix tailTrace_1030085
  have hstable : (prefixWord ++ tailWord_1030085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030085).length < 2 ^ (prefixWord ++ tailWord_1030085).sum := by decide
  have hdescent : baseEnd_1030085 < baseStart_1030085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030129 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 6]
def baseStart_1030129 : Nat := 118140960795 + 1030129 * 2 ^ 59
def prefixEnd_1030129 : Nat := 4983230072969 + 3 ^ 40 * 1030129 * 2
def baseEnd_1030129 : Nat := 58772368126167261027781

theorem tailTrace_1030129 : CollatzResearch.WordTrace tailWord_1030129 prefixEnd_1030129 58772368126167261027781 := by
  unfold tailWord_1030129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37571891285026039871645441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25047927523350693247763627 37571891285026039871645441)
  ·
    refine ⟨28178918463769529903734081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37571891285026039871645441 28178918463769529903734081)
    ·
      refine ⟨21134188847827147427800561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28178918463769529903734081 21134188847827147427800561)
      ·
        refine ⟨15850641635870360570850421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21134188847827147427800561 15850641635870360570850421)
        ·
          refine ⟨1485997653362846303517227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15850641635870360570850421 1485997653362846303517227)
          ·
            refine ⟨2228996480044269455275841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485997653362846303517227 2228996480044269455275841)
            ·
              refine ⟨1671747360033202091456881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228996480044269455275841 1671747360033202091456881)
              ·
                refine ⟨1253810520024901568592661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671747360033202091456881 1253810520024901568592661)
                ·
                  refine ⟨58772368126167261027781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253810520024901568592661 58772368126167261027781)
                  ·
                    rfl

theorem cell23_1030129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_1030129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030129 prefixEnd_1030129 := by exact prefixLift 1030129
  have htrace : WordTrace (prefixWord ++ tailWord_1030129) baseStart_1030129 baseEnd_1030129 := by
    simpa [prefixWord, tailWord_1030129, baseEnd_1030129] using wordTrace_append hprefix tailTrace_1030129
  have hstable : (prefixWord ++ tailWord_1030129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030129).length < 2 ^ (prefixWord ++ tailWord_1030129).sum := by decide
  have hdescent : baseEnd_1030129 < baseStart_1030129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030135 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1030135 : Nat := 118140960795 + 1030135 * 2 ^ 59
def prefixEnd_1030135 : Nat := 4983230072969 + 3 ^ 40 * 1030135 * 2
def baseEnd_1030135 : Nat := 528954394019432325775001

theorem tailTrace_1030135 : CollatzResearch.WordTrace tailWord_1030135 prefixEnd_1030135 528954394019432325775001 := by
  unfold tailWord_1030135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37572110123004302896363859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25048073415336201930909239 37572110123004302896363859)
  ·
    refine ⟨56358165184506454344545789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37572110123004302896363859 56358165184506454344545789)
    ·
      refine ⟨21134311944189920379204671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56358165184506454344545789 21134311944189920379204671)
      ·
        refine ⟨31701467916284880568807007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21134311944189920379204671 31701467916284880568807007)
        ·
          refine ⟨47552201874427320853210511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31701467916284880568807007 47552201874427320853210511)
          ·
            refine ⟨71328302811640981279815767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47552201874427320853210511 71328302811640981279815767)
            ·
              refine ⟨106992454217461471919723651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71328302811640981279815767 106992454217461471919723651)
              ·
                refine ⟨160488681326192207879585477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106992454217461471919723651 160488681326192207879585477)
                ·
                  refine ⟨30091627748661038977422277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160488681326192207879585477 30091627748661038977422277)
                  ·
                    refine ⟨5642180202873944808266677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30091627748661038977422277 5642180202873944808266677)
                    ·
                      refine ⟨528954394019432325775001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5642180202873944808266677 528954394019432325775001)
                      ·
                        rfl

theorem cell23_1030135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1030135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030135 prefixEnd_1030135 := by exact prefixLift 1030135
  have htrace : WordTrace (prefixWord ++ tailWord_1030135) baseStart_1030135 baseEnd_1030135 := by
    simpa [prefixWord, tailWord_1030135, baseEnd_1030135] using wordTrace_append hprefix tailTrace_1030135
  have hstable : (prefixWord ++ tailWord_1030135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030135).length < 2 ^ (prefixWord ++ tailWord_1030135).sum := by decide
  have hdescent : baseEnd_1030135 < baseStart_1030135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030157 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1030157 : Nat := 118140960795 + 1030157 * 2 ^ 59
def prefixEnd_1030157 : Nat := 4983230072969 + 3 ^ 40 * 1030157 * 2
def baseEnd_1030157 : Nat := 528965690593831239699901

theorem tailTrace_1030157 : CollatzResearch.WordTrace tailWord_1030157 prefixEnd_1030157 528965690593831239699901 := by
  unfold tailWord_1030157
  simp only [CollatzResearch.WordTrace]
  refine ⟨37572912528924600653664725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25048608352616400435776483 37572912528924600653664725)
  ·
    refine ⟨880615137396670327820267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37572912528924600653664725 880615137396670327820267)
    ·
      refine ⟨1320922706095005491730401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880615137396670327820267 1320922706095005491730401)
      ·
        refine ⟨990692029571254118797801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1320922706095005491730401 990692029571254118797801)
        ·
          refine ⟨743019022178440589098351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990692029571254118797801 743019022178440589098351)
          ·
            refine ⟨1114528533267660883647527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743019022178440589098351 1114528533267660883647527)
            ·
              refine ⟨1671792799901491325471291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114528533267660883647527 1671792799901491325471291)
              ·
                refine ⟨2507689199852236988206937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671792799901491325471291 2507689199852236988206937)
                ·
                  refine ⟨1880766899889177741155203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507689199852236988206937 1880766899889177741155203)
                  ·
                    refine ⟨2821150349833766611732805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880766899889177741155203 2821150349833766611732805)
                    ·
                      refine ⟨528965690593831239699901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2821150349833766611732805 528965690593831239699901)
                      ·
                        rfl

theorem cell23_1030157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1030157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030157 prefixEnd_1030157 := by exact prefixLift 1030157
  have htrace : WordTrace (prefixWord ++ tailWord_1030157) baseStart_1030157 baseEnd_1030157 := by
    simpa [prefixWord, tailWord_1030157, baseEnd_1030157] using wordTrace_append hprefix tailTrace_1030157
  have hstable : (prefixWord ++ tailWord_1030157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030157).length < 2 ^ (prefixWord ++ tailWord_1030157).sum := by decide
  have hdescent : baseEnd_1030157 < baseStart_1030157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030173 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1030173 : Nat := 118140960795 + 1030173 * 2 ^ 59
def prefixEnd_1030173 : Nat := 4983230072969 + 3 ^ 40 * 1030173 * 2
def baseEnd_1030173 : Nat := 528973906284303177099827

theorem tailTrace_1030173 : CollatzResearch.WordTrace tailWord_1030173 prefixEnd_1030173 528973906284303177099827 := by
  unfold tailWord_1030173
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573496096866635386247173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25048997397911090257498115 37573496096866635386247173)
  ·
    refine ⟨7045030518162494134921345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37573496096866635386247173 7045030518162494134921345)
    ·
      refine ⟨5283772888621870601191009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7045030518162494134921345 5283772888621870601191009)
      ·
        refine ⟨3962829666466402950893257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283772888621870601191009 3962829666466402950893257)
        ·
          refine ⟨2972122249849802213169943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962829666466402950893257 2972122249849802213169943)
          ·
            refine ⟨4458183374774703319754915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972122249849802213169943 4458183374774703319754915)
            ·
              refine ⟨6687275062162054979632373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458183374774703319754915 6687275062162054979632373)
              ·
                refine ⟨626932037077692654340535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6687275062162054979632373 626932037077692654340535)
                ·
                  refine ⟨940398055616538981510803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626932037077692654340535 940398055616538981510803)
                  ·
                    refine ⟨1410597083424808472266205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940398055616538981510803 1410597083424808472266205)
                    ·
                      refine ⟨528973906284303177099827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410597083424808472266205 528973906284303177099827)
                      ·
                        rfl

theorem cell23_1030173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1030173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030173 prefixEnd_1030173 := by exact prefixLift 1030173
  have htrace : WordTrace (prefixWord ++ tailWord_1030173) baseStart_1030173 baseEnd_1030173 := by
    simpa [prefixWord, tailWord_1030173, baseEnd_1030173] using wordTrace_append hprefix tailTrace_1030173
  have hstable : (prefixWord ++ tailWord_1030173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030173).length < 2 ^ (prefixWord ++ tailWord_1030173).sum := by decide
  have hdescent : baseEnd_1030173 < baseStart_1030173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030179 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 4]
def baseStart_1030179 : Nat := 118140960795 + 1030179 * 2 ^ 59
def prefixEnd_1030179 : Nat := 4983230072969 + 3 ^ 40 * 1030179 * 2
def baseEnd_1030179 : Nat := 528976987168230153624799

theorem tailTrace_1030179 : CollatzResearch.WordTrace tailWord_1030179 prefixEnd_1030179 528976987168230153624799 := by
  unfold tailWord_1030179
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573714934844898410965591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25049143289896598940643727 37573714934844898410965591)
  ·
    refine ⟨56360572402267347616448387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37573714934844898410965591 56360572402267347616448387)
    ·
      refine ⟨84540858603401021424672581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56360572402267347616448387 84540858603401021424672581)
      ·
        refine ⟨15851410988137691517126109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84540858603401021424672581 15851410988137691517126109)
        ·
          refine ⟨5944279120551634318922291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15851410988137691517126109 5944279120551634318922291)
          ·
            refine ⟨8916418680827451478383437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944279120551634318922291 8916418680827451478383437)
            ·
              refine ⟨3343657005310294304393789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8916418680827451478383437 3343657005310294304393789)
              ·
                refine ⟨1253871376991360364147671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343657005310294304393789 1253871376991360364147671)
                ·
                  refine ⟨1880807065487040546221507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253871376991360364147671 1880807065487040546221507)
                  ·
                    refine ⟨2821210598230560819332261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880807065487040546221507 2821210598230560819332261)
                    ·
                      refine ⟨528976987168230153624799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2821210598230560819332261 528976987168230153624799)
                      ·
                        rfl

theorem cell23_1030179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_1030179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030179 prefixEnd_1030179 := by exact prefixLift 1030179
  have htrace : WordTrace (prefixWord ++ tailWord_1030179) baseStart_1030179 baseEnd_1030179 := by
    simpa [prefixWord, tailWord_1030179, baseEnd_1030179] using wordTrace_append hprefix tailTrace_1030179
  have hstable : (prefixWord ++ tailWord_1030179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030179).length < 2 ^ (prefixWord ++ tailWord_1030179).sum := by decide
  have hdescent : baseEnd_1030179 < baseStart_1030179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030209 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1030209 : Nat := 118140960795 + 1030209 * 2 ^ 59
def prefixEnd_1030209 : Nat := 4983230072969 + 3 ^ 40 * 1030209 * 2
def baseEnd_1030209 : Nat := 528992391587865036249661

theorem tailTrace_1030209 : CollatzResearch.WordTrace tailWord_1030209 prefixEnd_1030209 528992391587865036249661 := by
  unfold tailWord_1030209
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574809124736213534557681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25049872749824142356371787 37574809124736213534557681)
  ·
    refine ⟨28181106843552160150918261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37574809124736213534557681 28181106843552160150918261)
    ·
      refine ⟨2641978766583015014148587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28181106843552160150918261 2641978766583015014148587)
      ·
        refine ⟨3962968149874522521222881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641978766583015014148587 3962968149874522521222881)
        ·
          refine ⟨2972226112405891890917161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962968149874522521222881 2972226112405891890917161)
          ·
            refine ⟨2229169584304418918187871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972226112405891890917161 2229169584304418918187871)
            ·
              refine ⟨3343754376456628377281807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229169584304418918187871 3343754376456628377281807)
              ·
                refine ⟨5015631564684942565922711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343754376456628377281807 5015631564684942565922711)
                ·
                  refine ⟨7523447347027413848884067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015631564684942565922711 7523447347027413848884067)
                  ·
                    refine ⟨11285171020541120773326101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7523447347027413848884067 11285171020541120773326101)
                    ·
                      refine ⟨528992391587865036249661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11285171020541120773326101 528992391587865036249661)
                      ·
                        rfl

theorem cell23_1030209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1030209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030209 prefixEnd_1030209 := by exact prefixLift 1030209
  have htrace : WordTrace (prefixWord ++ tailWord_1030209) baseStart_1030209 baseEnd_1030209 := by
    simpa [prefixWord, tailWord_1030209, baseEnd_1030209] using wordTrace_append hprefix tailTrace_1030209
  have hstable : (prefixWord ++ tailWord_1030209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030209).length < 2 ^ (prefixWord ++ tailWord_1030209).sum := by decide
  have hdescent : baseEnd_1030209 < baseStart_1030209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030263 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_1030263 : Nat := 118140960795 + 1030263 * 2 ^ 59
def prefixEnd_1030263 : Nat := 4983230072969 + 3 ^ 40 * 1030263 * 2
def baseEnd_1030263 : Nat := 529020119543207824974413

theorem tailTrace_1030263 : CollatzResearch.WordTrace tailWord_1030263 prefixEnd_1030263 529020119543207824974413 := by
  unfold tailWord_1030263
  simp only [CollatzResearch.WordTrace]
  refine ⟨37576778666540580757023443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25051185777693720504682295 37576778666540580757023443)
  ·
    refine ⟨56365167999810871135535165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37576778666540580757023443 56365167999810871135535165)
    ·
      refine ⟨21136937999929076675825687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56365167999810871135535165 21136937999929076675825687)
      ·
        refine ⟨31705406999893615013738531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136937999929076675825687 31705406999893615013738531)
        ·
          refine ⟨47558110499840422520607797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31705406999893615013738531 47558110499840422520607797)
          ·
            refine ⟨4458572859360039611306981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47558110499840422520607797 4458572859360039611306981)
            ·
              refine ⟨835982411130007427120059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4458572859360039611306981 835982411130007427120059)
              ·
                refine ⟨1253973616695011140680089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835982411130007427120059 1253973616695011140680089)
                ·
                  refine ⟨940480212521258355510067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253973616695011140680089 940480212521258355510067)
                  ·
                    refine ⟨1410720318781887533265101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940480212521258355510067 1410720318781887533265101)
                    ·
                      refine ⟨529020119543207824974413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410720318781887533265101 529020119543207824974413)
                      ·
                        rfl

theorem cell23_1030263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_1030263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030263 prefixEnd_1030263 := by exact prefixLift 1030263
  have htrace : WordTrace (prefixWord ++ tailWord_1030263) baseStart_1030263 baseEnd_1030263 := by
    simpa [prefixWord, tailWord_1030263, baseEnd_1030263] using wordTrace_append hprefix tailTrace_1030263
  have hstable : (prefixWord ++ tailWord_1030263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030263).length < 2 ^ (prefixWord ++ tailWord_1030263).sum := by decide
  have hdescent : baseEnd_1030263 < baseStart_1030263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030273 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_1030273 : Nat := 118140960795 + 1030273 * 2 ^ 59
def prefixEnd_1030273 : Nat := 4983230072969 + 3 ^ 40 * 1030273 * 2
def baseEnd_1030273 : Nat := 529025254349752785849367

theorem tailTrace_1030273 : CollatzResearch.WordTrace tailWord_1030273 prefixEnd_1030273 529025254349752785849367 := by
  unfold tailWord_1030273
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577143396504352464887473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25051428931002901643258315 37577143396504352464887473)
  ·
    refine ⟨28182857547378264348665605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37577143396504352464887473 28182857547378264348665605)
    ·
      refine ⟨5284285790133424565374801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28182857547378264348665605 5284285790133424565374801)
      ·
        refine ⟨3963214342600068424031101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284285790133424565374801 3963214342600068424031101)
        ·
          refine ⟨1486205378475025659011663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3963214342600068424031101 1486205378475025659011663)
          ·
            refine ⟨2229308067712538488517495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486205378475025659011663 2229308067712538488517495)
            ·
              refine ⟨3343962101568807732776243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229308067712538488517495 3343962101568807732776243)
              ·
                refine ⟨5015943152353211599164365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343962101568807732776243 5015943152353211599164365)
                ·
                  refine ⟨1880978682132454349686637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5015943152353211599164365 1880978682132454349686637)
                  ·
                    refine ⟨705367005799670381132489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1880978682132454349686637 705367005799670381132489)
                    ·
                      refine ⟨529025254349752785849367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705367005799670381132489 529025254349752785849367)
                      ·
                        rfl

theorem cell23_1030273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_1030273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030273 prefixEnd_1030273 := by exact prefixLift 1030273
  have htrace : WordTrace (prefixWord ++ tailWord_1030273) baseStart_1030273 baseEnd_1030273 := by
    simpa [prefixWord, tailWord_1030273, baseEnd_1030273] using wordTrace_append hprefix tailTrace_1030273
  have hstable : (prefixWord ++ tailWord_1030273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030273).length < 2 ^ (prefixWord ++ tailWord_1030273).sum := by decide
  have hdescent : baseEnd_1030273 < baseStart_1030273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030290 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1030290 : Nat := 118140960795 + 1030290 * 2 ^ 59
def prefixEnd_1030290 : Nat := 4983230072969 + 3 ^ 40 * 1030290 * 2
def baseEnd_1030290 : Nat := 529033983520879219336789

theorem tailTrace_1030290 : CollatzResearch.WordTrace tailWord_1030290 prefixEnd_1030290 529033983520879219336789 := by
  unfold tailWord_1030290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394440859360691092064081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25051842291628509578837549 9394440859360691092064081)
  ·
    refine ⟨7045830644520518319048061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9394440859360691092064081 7045830644520518319048061)
    ·
      refine ⟨2642186491695194369643023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7045830644520518319048061 2642186491695194369643023)
      ·
        refine ⟨3963279737542791554464535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642186491695194369643023 3963279737542791554464535)
        ·
          refine ⟨5944919606314187331696803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963279737542791554464535 5944919606314187331696803)
          ·
            refine ⟨8917379409471280997545205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944919606314187331696803 8917379409471280997545205)
            ·
              refine ⟨836004319637932593519863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8917379409471280997545205 836004319637932593519863)
              ·
                refine ⟨1254006479456898890279795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836004319637932593519863 1254006479456898890279795)
                ·
                  refine ⟨1881009719185348335419693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254006479456898890279795 1881009719185348335419693)
                  ·
                    refine ⟨705378644694505625782385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881009719185348335419693 705378644694505625782385)
                    ·
                      refine ⟨529033983520879219336789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705378644694505625782385 529033983520879219336789)
                      ·
                        rfl

theorem cell23_1030290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1030290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030290 prefixEnd_1030290 := by exact prefixLift 1030290
  have htrace : WordTrace (prefixWord ++ tailWord_1030290) baseStart_1030290 baseEnd_1030290 := by
    simpa [prefixWord, tailWord_1030290, baseEnd_1030290] using wordTrace_append hprefix tailTrace_1030290
  have hstable : (prefixWord ++ tailWord_1030290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030290).length < 2 ^ (prefixWord ++ tailWord_1030290).sum := by decide
  have hdescent : baseEnd_1030290 < baseStart_1030290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030306 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1030306 : Nat := 118140960795 + 1030306 * 2 ^ 59
def prefixEnd_1030306 : Nat := 4983230072969 + 3 ^ 40 * 1030306 * 2
def baseEnd_1030306 : Nat := 529042199211351156736715

theorem tailTrace_1030306 : CollatzResearch.WordTrace tailWord_1030306 prefixEnd_1030306 529042199211351156736715 := by
  unfold tailWord_1030306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394586751346199775209693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25052231336923199400559181 9394586751346199775209693)
  ·
    refine ⟨3522970031754824915703635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9394586751346199775209693 3522970031754824915703635)
    ·
      refine ⟨5284455047632237373555453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522970031754824915703635 5284455047632237373555453)
      ·
        refine ⟨1981670642862089015083295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5284455047632237373555453 1981670642862089015083295)
        ·
          refine ⟨2972505964293133522624943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981670642862089015083295 2972505964293133522624943)
          ·
            refine ⟨4458758946439700283937415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972505964293133522624943 4458758946439700283937415)
            ·
              refine ⟨6688138419659550425906123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458758946439700283937415 6688138419659550425906123)
              ·
                refine ⟨10032207629489325638859185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688138419659550425906123 10032207629489325638859185)
                ·
                  refine ⟨7524155722116994229144389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032207629489325638859185 7524155722116994229144389)
                  ·
                    refine ⟨1410779197896936417964573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524155722116994229144389 1410779197896936417964573)
                    ·
                      refine ⟨529042199211351156736715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410779197896936417964573 529042199211351156736715)
                      ·
                        rfl

theorem cell23_1030306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1030306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030306 prefixEnd_1030306 := by exact prefixLift 1030306
  have htrace : WordTrace (prefixWord ++ tailWord_1030306) baseStart_1030306 baseEnd_1030306 := by
    simpa [prefixWord, tailWord_1030306, baseEnd_1030306] using wordTrace_append hprefix tailTrace_1030306
  have hstable : (prefixWord ++ tailWord_1030306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030306).length < 2 ^ (prefixWord ++ tailWord_1030306).sum := by decide
  have hdescent : baseEnd_1030306 < baseStart_1030306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030352 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_1030352 : Nat := 118140960795 + 1030352 * 2 ^ 59
def prefixEnd_1030352 : Nat := 4983230072969 + 3 ^ 40 * 1030352 * 2
def baseEnd_1030352 : Nat := 176355273107152658920501

theorem tailTrace_1030352 : CollatzResearch.WordTrace tailWord_1030352 prefixEnd_1030352 176355273107152658920501 := by
  unfold tailWord_1030352
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790012381609074478506655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25053349842145432638008873 18790012381609074478506655)
  ·
    refine ⟨28185018572413611717759983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18790012381609074478506655 28185018572413611717759983)
    ·
      refine ⟨42277527858620417576639975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28185018572413611717759983 42277527858620417576639975)
      ·
        refine ⟨63416291787930626364959963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42277527858620417576639975 63416291787930626364959963)
        ·
          refine ⟨95124437681895939547439945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63416291787930626364959963 95124437681895939547439945)
          ·
            refine ⟨71343328261421954660579959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95124437681895939547439945 71343328261421954660579959)
            ·
              refine ⟨107014992392132931990869939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71343328261421954660579959 107014992392132931990869939)
              ·
                refine ⟨160522488588199397986304909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107014992392132931990869939 160522488588199397986304909)
                ·
                  refine ⟨60195933220574774244864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160522488588199397986304909 60195933220574774244864341)
                  ·
                    refine ⟨176355273107152658920501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 60195933220574774244864341 176355273107152658920501)
                    ·
                      rfl

theorem cell23_1030352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_1030352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030352 prefixEnd_1030352 := by exact prefixLift 1030352
  have htrace : WordTrace (prefixWord ++ tailWord_1030352) baseStart_1030352 baseEnd_1030352 := by
    simpa [prefixWord, tailWord_1030352, baseEnd_1030352] using wordTrace_append hprefix tailTrace_1030352
  have hstable : (prefixWord ++ tailWord_1030352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030352).length < 2 ^ (prefixWord ++ tailWord_1030352).sum := by decide
  have hdescent : baseEnd_1030352 < baseStart_1030352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030359 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1030359 : Nat := 118140960795 + 1030359 * 2 ^ 59
def prefixEnd_1030359 : Nat := 4983230072969 + 3 ^ 40 * 1030359 * 2
def baseEnd_1030359 : Nat := 529069413686039449373971

theorem tailTrace_1030359 : CollatzResearch.WordTrace tailWord_1030359 prefixEnd_1030359 529069413686039449373971 := by
  unfold tailWord_1030359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580280074192789152518131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25053520049461859435012087 37580280074192789152518131)
  ·
    refine ⟨56370420111289183728777197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37580280074192789152518131 56370420111289183728777197)
    ·
      refine ⟨21138907541733443898291449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56370420111289183728777197 21138907541733443898291449)
      ·
        refine ⟨15854180656300082923718587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21138907541733443898291449 15854180656300082923718587)
        ·
          refine ⟨23781270984450124385577881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15854180656300082923718587 23781270984450124385577881)
          ·
            refine ⟨17835953238337593289183411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23781270984450124385577881 17835953238337593289183411)
            ·
              refine ⟨26753929857506389933775117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17835953238337593289183411 26753929857506389933775117)
              ·
                refine ⟨10032723696564896225165669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26753929857506389933775117 10032723696564896225165669)
                ·
                  refine ⟨1881135693105918042218563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10032723696564896225165669 1881135693105918042218563)
                  ·
                    refine ⟨2821703539658877063327845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881135693105918042218563 2821703539658877063327845)
                    ·
                      refine ⟨529069413686039449373971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2821703539658877063327845 529069413686039449373971)
                      ·
                        rfl

theorem cell23_1030359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1030359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030359 prefixEnd_1030359 := by exact prefixLift 1030359
  have htrace : WordTrace (prefixWord ++ tailWord_1030359) baseStart_1030359 baseEnd_1030359 := by
    simpa [prefixWord, tailWord_1030359, baseEnd_1030359] using wordTrace_append hprefix tailTrace_1030359
  have hstable : (prefixWord ++ tailWord_1030359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030359).length < 2 ^ (prefixWord ++ tailWord_1030359).sum := by decide
  have hdescent : baseEnd_1030359 < baseStart_1030359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030379 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3]
def baseStart_1030379 : Nat := 118140960795 + 1030379 * 2 ^ 59
def prefixEnd_1030379 : Nat := 4983230072969 + 3 ^ 40 * 1030379 * 2
def baseEnd_1030379 : Nat := 529079683299129371123879

theorem tailTrace_1030379 : CollatzResearch.WordTrace tailWord_1030379 prefixEnd_1030379 529079683299129371123879 := by
  unfold tailWord_1030379
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581009534120332568246191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25054006356080221712164127 37581009534120332568246191)
  ·
    refine ⟨56371514301180498852369287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37581009534120332568246191 56371514301180498852369287)
    ·
      refine ⟨84557271451770748278553931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56371514301180498852369287 84557271451770748278553931)
      ·
        refine ⟨126835907177656122417830897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84557271451770748278553931 126835907177656122417830897)
        ·
          refine ⟨95126930383242091813373173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126835907177656122417830897 95126930383242091813373173)
          ·
            refine ⟨8918149723428946107503735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95126930383242091813373173 8918149723428946107503735)
            ·
              refine ⟨13377224585143419161255603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918149723428946107503735 13377224585143419161255603)
              ·
                refine ⟨20065836877715128741883405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13377224585143419161255603 20065836877715128741883405)
                ·
                  refine ⟨7524688829143173278206277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20065836877715128741883405 7524688829143173278206277)
                  ·
                    refine ⟨1410879155464344989663677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524688829143173278206277 1410879155464344989663677)
                    ·
                      refine ⟨529079683299129371123879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410879155464344989663677 529079683299129371123879)
                      ·
                        rfl

theorem cell23_1030379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].length) (baseStart_1030379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030379 prefixEnd_1030379 := by exact prefixLift 1030379
  have htrace : WordTrace (prefixWord ++ tailWord_1030379) baseStart_1030379 baseEnd_1030379 := by
    simpa [prefixWord, tailWord_1030379, baseEnd_1030379] using wordTrace_append hprefix tailTrace_1030379
  have hstable : (prefixWord ++ tailWord_1030379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030379).length < 2 ^ (prefixWord ++ tailWord_1030379).sum := by decide
  have hdescent : baseEnd_1030379 < baseStart_1030379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030396 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_1030396 : Nat := 118140960795 + 1030396 * 2 ^ 59
def prefixEnd_1030396 : Nat := 4983230072969 + 3 ^ 40 * 1030396 * 2
def baseEnd_1030396 : Nat := 529088412470255804611301

theorem tailTrace_1030396 : CollatzResearch.WordTrace tailWord_1030396 prefixEnd_1030396 529088412470255804611301 := by
  unfold tailWord_1030396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790814787529372235807521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25054419716705829647743361 18790814787529372235807521)
  ·
    refine ⟨14093111090647029176855641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18790814787529372235807521 14093111090647029176855641)
    ·
      refine ⟨10569833317985271882641731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14093111090647029176855641 10569833317985271882641731)
      ·
        refine ⟨15854749976977907823962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10569833317985271882641731 15854749976977907823962597)
        ·
          refine ⟨2972765620683357716992987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15854749976977907823962597 2972765620683357716992987)
          ·
            refine ⟨4459148431025036575489481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972765620683357716992987 4459148431025036575489481)
            ·
              refine ⟨3344361323268777431617111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459148431025036575489481 3344361323268777431617111)
              ·
                refine ⟨5016541984903166147425667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344361323268777431617111 5016541984903166147425667)
                ·
                  refine ⟨7524812977354749221138501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016541984903166147425667 7524812977354749221138501)
                  ·
                    refine ⟨1410902433254015478963469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524812977354749221138501 1410902433254015478963469)
                    ·
                      refine ⟨529088412470255804611301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410902433254015478963469 529088412470255804611301)
                      ·
                        rfl

theorem cell23_1030396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_1030396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030396 prefixEnd_1030396 := by exact prefixLift 1030396
  have htrace : WordTrace (prefixWord ++ tailWord_1030396) baseStart_1030396 baseEnd_1030396 := by
    simpa [prefixWord, tailWord_1030396, baseEnd_1030396] using wordTrace_append hprefix tailTrace_1030396
  have hstable : (prefixWord ++ tailWord_1030396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030396).length < 2 ^ (prefixWord ++ tailWord_1030396).sum := by decide
  have hdescent : baseEnd_1030396 < baseStart_1030396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030460 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_1030460 : Nat := 118140960795 + 1030460 * 2 ^ 59
def prefixEnd_1030460 : Nat := 4983230072969 + 3 ^ 40 * 1030460 * 2
def baseEnd_1030460 : Nat := 529121275232143554211007

theorem tailTrace_1030460 : CollatzResearch.WordTrace tailWord_1030460 prefixEnd_1030460 529121275232143554211007 := by
  unfold tailWord_1030460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18791981923413441700972417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25055975897884588934629889 18791981923413441700972417)
  ·
    refine ⟨14093986442560081275729313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18791981923413441700972417 14093986442560081275729313)
    ·
      refine ⟨10570489831920060956796985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14093986442560081275729313 10570489831920060956796985)
      ·
        refine ⟨7927867373940045717597739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10570489831920060956796985 7927867373940045717597739)
        ·
          refine ⟨11891801060910068576396609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927867373940045717597739 11891801060910068576396609)
          ·
            refine ⟨8918850795682551432297457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11891801060910068576396609 8918850795682551432297457)
            ·
              refine ⟨6689138096761913574223093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8918850795682551432297457 6689138096761913574223093)
              ·
                refine ⟨627106696571429397583415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6689138096761913574223093 627106696571429397583415)
                ·
                  refine ⟨940660044857144096375123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627106696571429397583415 940660044857144096375123)
                  ·
                    refine ⟨1410990067285716144562685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940660044857144096375123 1410990067285716144562685)
                    ·
                      refine ⟨529121275232143554211007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1410990067285716144562685 529121275232143554211007)
                      ·
                        rfl

theorem cell23_1030460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_1030460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030460 prefixEnd_1030460 := by exact prefixLift 1030460
  have htrace : WordTrace (prefixWord ++ tailWord_1030460) baseStart_1030460 baseEnd_1030460 := by
    simpa [prefixWord, tailWord_1030460, baseEnd_1030460] using wordTrace_append hprefix tailTrace_1030460
  have hstable : (prefixWord ++ tailWord_1030460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030460).length < 2 ^ (prefixWord ++ tailWord_1030460).sum := by decide
  have hdescent : baseEnd_1030460 < baseStart_1030460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030463 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 1, 5]
def baseStart_1030463 : Nat := 118140960795 + 1030463 * 2 ^ 59
def prefixEnd_1030463 : Nat := 4983230072969 + 3 ^ 40 * 1030463 * 2
def baseEnd_1030463 : Nat := 176374271891369014157831

theorem tailTrace_1030463 : CollatzResearch.WordTrace tailWord_1030463 prefixEnd_1030463 176374271891369014157831 := by
  unfold tailWord_1030463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37584073265816014914304043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25056048843877343276202695 37584073265816014914304043)
  ·
    refine ⟨56376109898724022371456065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37584073265816014914304043 56376109898724022371456065)
    ·
      refine ⟨42282082424043016778592049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56376109898724022371456065 42282082424043016778592049)
      ·
        refine ⟨31711561818032262583944037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42282082424043016778592049 31711561818032262583944037)
        ·
          refine ⟨5945917840881049234489507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31711561818032262583944037 5945917840881049234489507)
          ·
            refine ⟨8918876761321573851734261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945917840881049234489507 8918876761321573851734261)
            ·
              refine ⟨836144696373897548600087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8918876761321573851734261 836144696373897548600087)
              ·
                refine ⟨1254217044560846322900131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836144696373897548600087 1254217044560846322900131)
                ·
                  refine ⟨1881325566841269484350197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254217044560846322900131 1881325566841269484350197)
                  ·
                    refine ⟨176374271891369014157831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1881325566841269484350197 176374271891369014157831)
                    ·
                      rfl

theorem cell23_1030463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_1030463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030463 prefixEnd_1030463 := by exact prefixLift 1030463
  have htrace : WordTrace (prefixWord ++ tailWord_1030463) baseStart_1030463 baseEnd_1030463 := by
    simpa [prefixWord, tailWord_1030463, baseEnd_1030463] using wordTrace_append hprefix tailTrace_1030463
  have hstable : (prefixWord ++ tailWord_1030463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030463).length < 2 ^ (prefixWord ++ tailWord_1030463).sum := by decide
  have hdescent : baseEnd_1030463 < baseStart_1030463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030479 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1030479 : Nat := 118140960795 + 1030479 * 2 ^ 59
def prefixEnd_1030479 : Nat := 4983230072969 + 3 ^ 40 * 1030479 * 2
def baseEnd_1030479 : Nat := 529131031364578979873419

theorem tailTrace_1030479 : CollatzResearch.WordTrace tailWord_1030479 prefixEnd_1030479 529131031364578979873419 := by
  unfold tailWord_1030479
  simp only [CollatzResearch.WordTrace]
  refine ⟨37584656833758049646886491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25056437889172033097924327 37584656833758049646886491)
  ·
    refine ⟨56376985250637074470329737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37584656833758049646886491 56376985250637074470329737)
    ·
      refine ⟨42282738937977805852747303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56376985250637074470329737 42282738937977805852747303)
      ·
        refine ⟨63424108406966708779120955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42282738937977805852747303 63424108406966708779120955)
        ·
          refine ⟨95136162610450063168681433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63424108406966708779120955 95136162610450063168681433)
          ·
            refine ⟨71352121957837547376511075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95136162610450063168681433 71352121957837547376511075)
            ·
              refine ⟨107028182936756321064766613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71352121957837547376511075 107028182936756321064766613)
              ·
                refine ⟨5016946075160452549910935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107028182936756321064766613 5016946075160452549910935)
                ·
                  refine ⟨7525419112740678824866403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016946075160452549910935 7525419112740678824866403)
                  ·
                    refine ⟨11288128669111018237299605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525419112740678824866403 11288128669111018237299605)
                    ·
                      refine ⟨529131031364578979873419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11288128669111018237299605 529131031364578979873419)
                      ·
                        rfl

theorem cell23_1030479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1030479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030479 prefixEnd_1030479 := by exact prefixLift 1030479
  have htrace : WordTrace (prefixWord ++ tailWord_1030479) baseStart_1030479 baseEnd_1030479 := by
    simpa [prefixWord, tailWord_1030479, baseEnd_1030479] using wordTrace_append hprefix tailTrace_1030479
  have hstable : (prefixWord ++ tailWord_1030479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030479).length < 2 ^ (prefixWord ++ tailWord_1030479).sum := by decide
  have hdescent : baseEnd_1030479 < baseStart_1030479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030500 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_1030500 : Nat := 118140960795 + 1030500 * 2 ^ 59
def prefixEnd_1030500 : Nat := 4983230072969 + 3 ^ 40 * 1030500 * 2
def baseEnd_1030500 : Nat := 529141814458323397710823

theorem tailTrace_1030500 : CollatzResearch.WordTrace tailWord_1030500 prefixEnd_1030500 529141814458323397710823 := by
  unfold tailWord_1030500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792711383340985116700477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25056948511121313488933969 18792711383340985116700477)
  ·
    refine ⟨7047266768752869418762679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18792711383340985116700477 7047266768752869418762679)
    ·
      refine ⟨10570900153129304128144019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7047266768752869418762679 10570900153129304128144019)
      ·
        refine ⟨15856350229693956192216029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10570900153129304128144019 15856350229693956192216029)
        ·
          refine ⟨5946131336135233572081011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15856350229693956192216029 5946131336135233572081011)
          ·
            refine ⟨8919197004202850358121517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946131336135233572081011 8919197004202850358121517)
            ·
              refine ⟨3344698876576068884295569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8919197004202850358121517 3344698876576068884295569)
              ·
                refine ⟨2508524157432051663221677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344698876576068884295569 2508524157432051663221677)
                ·
                  refine ⟨940696559037019373708129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2508524157432051663221677 940696559037019373708129)
                  ·
                    refine ⟨705522419277764530281097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 940696559037019373708129 705522419277764530281097)
                    ·
                      refine ⟨529141814458323397710823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705522419277764530281097 529141814458323397710823)
                      ·
                        rfl

theorem cell23_1030500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_1030500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030500 prefixEnd_1030500 := by exact prefixLift 1030500
  have htrace : WordTrace (prefixWord ++ tailWord_1030500) baseStart_1030500 baseEnd_1030500 := by
    simpa [prefixWord, tailWord_1030500, baseEnd_1030500] using wordTrace_append hprefix tailTrace_1030500
  have hstable : (prefixWord ++ tailWord_1030500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030500).length < 2 ^ (prefixWord ++ tailWord_1030500).sum := by decide
  have hdescent : baseEnd_1030500 < baseStart_1030500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030503 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1030503 : Nat := 118140960795 + 1030503 * 2 ^ 59
def prefixEnd_1030503 : Nat := 4983230072969 + 3 ^ 40 * 1030503 * 2
def baseEnd_1030503 : Nat := 529143354900286885973309

theorem tailTrace_1030503 : CollatzResearch.WordTrace tailWord_1030503 prefixEnd_1030503 529143354900286885973309 := by
  unfold tailWord_1030503
  simp only [CollatzResearch.WordTrace]
  refine ⟨37585532185671101745760163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057021457114067830506775 37585532185671101745760163)
  ·
    refine ⟨56378298278506652618640245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37585532185671101745760163 56378298278506652618640245)
    ·
      refine ⟨5285465463609998682997523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56378298278506652618640245 5285465463609998682997523)
      ·
        refine ⟨7928198195414998024496285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285465463609998682997523 7928198195414998024496285)
        ·
          refine ⟨2973074323280624259186107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7928198195414998024496285 2973074323280624259186107)
          ·
            refine ⟨4459611484920936388779161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973074323280624259186107 4459611484920936388779161)
            ·
              refine ⟨3344708613690702291584371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459611484920936388779161 3344708613690702291584371)
              ·
                refine ⟨5017062920536053437376557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344708613690702291584371 5017062920536053437376557)
                ·
                  refine ⟨1881398595201020039016209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5017062920536053437376557 1881398595201020039016209)
                  ·
                    refine ⟨1411048946400765029262157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881398595201020039016209 1411048946400765029262157)
                    ·
                      refine ⟨529143354900286885973309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411048946400765029262157 529143354900286885973309)
                      ·
                        rfl

theorem cell23_1030503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1030503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030503 prefixEnd_1030503 := by exact prefixLift 1030503
  have htrace : WordTrace (prefixWord ++ tailWord_1030503) baseStart_1030503 baseEnd_1030503 := by
    simpa [prefixWord, tailWord_1030503, baseEnd_1030503] using wordTrace_append hprefix tailTrace_1030503
  have hstable : (prefixWord ++ tailWord_1030503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030503).length < 2 ^ (prefixWord ++ tailWord_1030503).sum := by decide
  have hdescent : baseEnd_1030503 < baseStart_1030503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030517 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1030517 : Nat := 118140960795 + 1030517 * 2 ^ 59
def prefixEnd_1030517 : Nat := 4983230072969 + 3 ^ 40 * 1030517 * 2
def baseEnd_1030517 : Nat := 529150543629449831198245

theorem tailTrace_1030517 : CollatzResearch.WordTrace tailWord_1030517 prefixEnd_1030517 529150543629449831198245 := by
  unfold tailWord_1030517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37586042807620382136769805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057361871746921424513203 37586042807620382136769805)
  ·
    refine ⟨14094766052857643301288677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37586042807620382136769805 14094766052857643301288677)
    ·
      refine ⟨2642768634910808118991627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14094766052857643301288677 2642768634910808118991627)
      ·
        refine ⟨3964152952366212178487441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642768634910808118991627 3964152952366212178487441)
        ·
          refine ⟨2973114714274659133865581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964152952366212178487441 2973114714274659133865581)
          ·
            refine ⟨1114918017852997175199593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2973114714274659133865581 1114918017852997175199593)
            ·
              refine ⟨836188513389747881399695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114918017852997175199593 836188513389747881399695)
              ·
                refine ⟨1254282770084621822099543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836188513389747881399695 1254282770084621822099543)
                ·
                  refine ⟨1881424155126932733149315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254282770084621822099543 1881424155126932733149315)
                  ·
                    refine ⟨2822136232690399099723973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881424155126932733149315 2822136232690399099723973)
                    ·
                      refine ⟨529150543629449831198245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2822136232690399099723973 529150543629449831198245)
                      ·
                        rfl

theorem cell23_1030517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1030517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030517 prefixEnd_1030517 := by exact prefixLift 1030517
  have htrace : WordTrace (prefixWord ++ tailWord_1030517) baseStart_1030517 baseEnd_1030517 := by
    simpa [prefixWord, tailWord_1030517, baseEnd_1030517] using wordTrace_append hprefix tailTrace_1030517
  have hstable : (prefixWord ++ tailWord_1030517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030517).length < 2 ^ (prefixWord ++ tailWord_1030517).sum := by decide
  have hdescent : baseEnd_1030517 < baseStart_1030517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030519 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 9]
def baseStart_1030519 : Nat := 118140960795 + 1030519 * 2 ^ 59
def prefixEnd_1030519 : Nat := 4983230072969 + 3 ^ 40 * 1030519 * 2
def baseEnd_1030519 : Nat := 176383856863586274457745

theorem tailTrace_1030519 : CollatzResearch.WordTrace tailWord_1030519 prefixEnd_1030519 176383856863586274457745 := by
  unfold tailWord_1030519
  simp only [CollatzResearch.WordTrace]
  refine ⟨37586115753613136478342611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057410502408757652228407 37586115753613136478342611)
  ·
    refine ⟨56379173630419704717513917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37586115753613136478342611 56379173630419704717513917)
    ·
      refine ⟨21142190111407389269067719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56379173630419704717513917 21142190111407389269067719)
      ·
        refine ⟨31713285167111083903601579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21142190111407389269067719 31713285167111083903601579)
        ·
          refine ⟨47569927750666625855402369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31713285167111083903601579 47569927750666625855402369)
          ·
            refine ⟨35677445812999969391551777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47569927750666625855402369 35677445812999969391551777)
            ·
              refine ⟨26758084359749977043663833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35677445812999969391551777 26758084359749977043663833)
              ·
                refine ⟨20068563269812482782747875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26758084359749977043663833 20068563269812482782747875)
                ·
                  refine ⟨30102844904718724174121813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20068563269812482782747875 30102844904718724174121813)
                  ·
                    refine ⟨176383856863586274457745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30102844904718724174121813 176383856863586274457745)
                    ·
                      rfl

theorem cell23_1030519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_1030519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030519 prefixEnd_1030519 := by exact prefixLift 1030519
  have htrace : WordTrace (prefixWord ++ tailWord_1030519) baseStart_1030519 baseEnd_1030519 := by
    simpa [prefixWord, tailWord_1030519, baseEnd_1030519] using wordTrace_append hprefix tailTrace_1030519
  have hstable : (prefixWord ++ tailWord_1030519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030519).length < 2 ^ (prefixWord ++ tailWord_1030519).sum := by decide
  have hdescent : baseEnd_1030519 < baseStart_1030519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030560 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2]
def baseStart_1030560 : Nat := 118140960795 + 1030560 * 2 ^ 59
def prefixEnd_1030560 : Nat := 4983230072969 + 3 ^ 40 * 1030560 * 2
def baseEnd_1030560 : Nat := 529172623297593162960547

theorem tailTrace_1030560 : CollatzResearch.WordTrace tailWord_1030560 prefixEnd_1030560 529172623297593162960547 := by
  unfold tailWord_1030560
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793805573232300240292567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25058407430976400320390089 18793805573232300240292567)
  ·
    refine ⟨28190708359848450360438851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18793805573232300240292567 28190708359848450360438851)
    ·
      refine ⟨42286062539772675540658277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28190708359848450360438851 42286062539772675540658277)
      ·
        refine ⟨7928636726207376663873427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42286062539772675540658277 7928636726207376663873427)
        ·
          refine ⟨11892955089311064995810141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928636726207376663873427 11892955089311064995810141)
          ·
            refine ⟨4459858158491649373428803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11892955089311064995810141 4459858158491649373428803)
            ·
              refine ⟨6689787237737474060143205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459858158491649373428803 6689787237737474060143205)
              ·
                refine ⟨1254335107075776386276851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6689787237737474060143205 1254335107075776386276851)
                ·
                  refine ⟨1881502660613664579415277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254335107075776386276851 1881502660613664579415277)
                  ·
                    refine ⟨705563497730124217280729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881502660613664579415277 705563497730124217280729)
                    ·
                      refine ⟨529172623297593162960547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705563497730124217280729 529172623297593162960547)
                      ·
                        rfl

theorem cell23_1030560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_1030560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030560 prefixEnd_1030560 := by exact prefixLift 1030560
  have htrace : WordTrace (prefixWord ++ tailWord_1030560) baseStart_1030560 baseEnd_1030560 := by
    simpa [prefixWord, tailWord_1030560, baseEnd_1030560] using wordTrace_append hprefix tailTrace_1030560
  have hstable : (prefixWord ++ tailWord_1030560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030560).length < 2 ^ (prefixWord ++ tailWord_1030560).sum := by decide
  have hdescent : baseEnd_1030560 < baseStart_1030560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030586 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1030586 : Nat := 118140960795 + 1030586 * 2 ^ 59
def prefixEnd_1030586 : Nat := 4983230072969 + 3 ^ 40 * 1030586 * 2
def baseEnd_1030586 : Nat := 529185973794610061235427

theorem tailTrace_1030586 : CollatzResearch.WordTrace tailWord_1030586 prefixEnd_1030586 529185973794610061235427 := by
  unfold tailWord_1030586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397139861092601730257903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25059039629580271280687741 9397139861092601730257903)
  ·
    refine ⟨14095709791638902595386855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9397139861092601730257903 14095709791638902595386855)
    ·
      refine ⟨21143564687458353893080283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14095709791638902595386855 21143564687458353893080283)
      ·
        refine ⟨31715347031187530839620425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21143564687458353893080283 31715347031187530839620425)
        ·
          refine ⟨23786510273390648129715319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31715347031187530839620425 23786510273390648129715319)
          ·
            refine ⟨35679765410085972194572979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23786510273390648129715319 35679765410085972194572979)
            ·
              refine ⟨53519648115128958291859469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35679765410085972194572979 53519648115128958291859469)
              ·
                refine ⟨20069868043173359359447301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53519648115128958291859469 20069868043173359359447301)
                ·
                  refine ⟨3763100258095004879896369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20069868043173359359447301 3763100258095004879896369)
                  ·
                    refine ⟨2822325193571253659922277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763100258095004879896369 2822325193571253659922277)
                    ·
                      refine ⟨529185973794610061235427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2822325193571253659922277 529185973794610061235427)
                      ·
                        rfl

theorem cell23_1030586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1030586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030586 prefixEnd_1030586 := by exact prefixLift 1030586
  have htrace : WordTrace (prefixWord ++ tailWord_1030586) baseStart_1030586 baseEnd_1030586 := by
    simpa [prefixWord, tailWord_1030586, baseEnd_1030586] using wordTrace_append hprefix tailTrace_1030586
  have hstable : (prefixWord ++ tailWord_1030586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030586).length < 2 ^ (prefixWord ++ tailWord_1030586).sum := by decide
  have hdescent : baseEnd_1030586 < baseStart_1030586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030636 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1030636 : Nat := 118140960795 + 1030636 * 2 ^ 59
def prefixEnd_1030636 : Nat := 4983230072969 + 3 ^ 40 * 1030636 * 2
def baseEnd_1030636 : Nat := 529211647827334865610197

theorem tailTrace_1030636 : CollatzResearch.WordTrace tailWord_1030636 prefixEnd_1030636 529211647827334865610197 := by
  unfold tailWord_1030636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795191547094632730175881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25060255396126176973567841 18795191547094632730175881)
  ·
    refine ⟨14096393660320974547631911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18795191547094632730175881 14096393660320974547631911)
    ·
      refine ⟨21144590490481461821447867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096393660320974547631911 21144590490481461821447867)
      ·
        refine ⟨31716885735722192732171801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21144590490481461821447867 31716885735722192732171801)
        ·
          refine ⟨23787664301791644549128851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31716885735722192732171801 23787664301791644549128851)
          ·
            refine ⟨35681496452687466823693277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23787664301791644549128851 35681496452687466823693277)
            ·
              refine ⟨13380561169757800058884979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35681496452687466823693277 13380561169757800058884979)
              ·
                refine ⟨20070841754636700088327469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380561169757800058884979 20070841754636700088327469)
                ·
                  refine ⟨7526565657988762533122801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20070841754636700088327469 7526565657988762533122801)
                  ·
                    refine ⟨5644924243491571899842101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526565657988762533122801 5644924243491571899842101)
                    ·
                      refine ⟨529211647827334865610197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5644924243491571899842101 529211647827334865610197)
                      ·
                        rfl

theorem cell23_1030636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1030636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030636 prefixEnd_1030636 := by exact prefixLift 1030636
  have htrace : WordTrace (prefixWord ++ tailWord_1030636) baseStart_1030636 baseEnd_1030636 := by
    simpa [prefixWord, tailWord_1030636, baseEnd_1030636] using wordTrace_append hprefix tailTrace_1030636
  have hstable : (prefixWord ++ tailWord_1030636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030636).length < 2 ^ (prefixWord ++ tailWord_1030636).sum := by decide
  have hdescent : baseEnd_1030636 < baseStart_1030636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030680 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1030680 : Nat := 118140960795 + 1030680 * 2 ^ 59
def prefixEnd_1030680 : Nat := 4983230072969 + 3 ^ 40 * 1030680 * 2
def baseEnd_1030680 : Nat := 529234240976132693459995

theorem tailTrace_1030680 : CollatzResearch.WordTrace tailWord_1030680 prefixEnd_1030680 529234240976132693459995 := by
  unfold tailWord_1030680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795993953014930487476747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25061325270686573983302329 18795993953014930487476747)
  ·
    refine ⟨28193990929522395731215121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18795993953014930487476747 28193990929522395731215121)
    ·
      refine ⟨21145493197141796798411341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28193990929522395731215121 21145493197141796798411341)
      ·
        refine ⟨7929559948928173799404253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21145493197141796798411341 7929559948928173799404253)
        ·
          refine ⟨2973584980848065174776595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7929559948928173799404253 2973584980848065174776595)
          ·
            refine ⟨4460377471272097762164893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973584980848065174776595 4460377471272097762164893)
            ·
              refine ⟨1672641551727036660811835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4460377471272097762164893 1672641551727036660811835)
              ·
                refine ⟨2508962327590554991217753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672641551727036660811835 2508962327590554991217753)
                ·
                  refine ⟨1881721745692916243413315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508962327590554991217753 1881721745692916243413315)
                  ·
                    refine ⟨2822582618539374365119973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881721745692916243413315 2822582618539374365119973)
                    ·
                      refine ⟨529234240976132693459995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2822582618539374365119973 529234240976132693459995)
                      ·
                        rfl

theorem cell23_1030680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1030680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030680 prefixEnd_1030680 := by exact prefixLift 1030680
  have htrace : WordTrace (prefixWord ++ tailWord_1030680) baseStart_1030680 baseEnd_1030680 := by
    simpa [prefixWord, tailWord_1030680, baseEnd_1030680] using wordTrace_append hprefix tailTrace_1030680
  have hstable : (prefixWord ++ tailWord_1030680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030680).length < 2 ^ (prefixWord ++ tailWord_1030680).sum := by decide
  have hdescent : baseEnd_1030680 < baseStart_1030680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030787 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 3, 2, 2]
def baseStart_1030787 : Nat := 118140960795 + 1030787 * 2 ^ 59
def prefixEnd_1030787 : Nat := 4983230072969 + 3 ^ 40 * 1030787 * 2
def baseEnd_1030787 : Nat := 529289183406163774822003

theorem tailTrace_1030787 : CollatzResearch.WordTrace tailWord_1030787 prefixEnd_1030787 529289183406163774822003 := by
  unfold tailWord_1030787
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595890516642218249098615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25063927011094812166065743 37595890516642218249098615)
  ·
    refine ⟨56393835774963327373647923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37595890516642218249098615 56393835774963327373647923)
    ·
      refine ⟨84590753662444991060471885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56393835774963327373647923 84590753662444991060471885)
      ·
        refine ⟨31721532623416871647676957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84590753662444991060471885 31721532623416871647676957)
        ·
          refine ⟨11895574733781326867878859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31721532623416871647676957 11895574733781326867878859)
          ·
            refine ⟨17843362100671990301818289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895574733781326867878859 17843362100671990301818289)
            ·
              refine ⟨13382521575503992726363717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17843362100671990301818289 13382521575503992726363717)
              ·
                refine ⟨2509222795406998636193197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13382521575503992726363717 2509222795406998636193197)
                ·
                  refine ⟨940958548277624488572449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2509222795406998636193197 940958548277624488572449)
                  ·
                    refine ⟨705718911208218366429337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 940958548277624488572449 705718911208218366429337)
                    ·
                      refine ⟨529289183406163774822003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705718911208218366429337 529289183406163774822003)
                      ·
                        rfl

theorem cell23_1030787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_1030787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030787 prefixEnd_1030787 := by exact prefixLift 1030787
  have htrace : WordTrace (prefixWord ++ tailWord_1030787) baseStart_1030787 baseEnd_1030787 := by
    simpa [prefixWord, tailWord_1030787, baseEnd_1030787] using wordTrace_append hprefix tailTrace_1030787
  have hstable : (prefixWord ++ tailWord_1030787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030787).length < 2 ^ (prefixWord ++ tailWord_1030787).sum := by decide
  have hdescent : baseEnd_1030787 < baseStart_1030787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030810 : List Nat := [3, 1, 1, 6, 1, 11]
def baseStart_1030810 : Nat := 118140960795 + 1030810 * 2 ^ 59
def prefixEnd_1030810 : Nat := 4983230072969 + 3 ^ 40 * 1030810 * 2
def baseEnd_1030810 : Nat := 2178193388729288826479

theorem tailTrace_1030810 : CollatzResearch.WordTrace tailWord_1030810 prefixEnd_1030810 2178193388729288826479 := by
  unfold tailWord_1030810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399182348889723294296471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25064486263705928784790589 9399182348889723294296471)
  ·
    refine ⟨14098773523334584941444707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399182348889723294296471 14098773523334584941444707)
    ·
      refine ⟨21148160285001877412167061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098773523334584941444707 21148160285001877412167061)
      ·
        refine ⟨991320013359463003695331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21148160285001877412167061 991320013359463003695331)
        ·
          refine ⟨1486980020039194505542997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991320013359463003695331 1486980020039194505542997)
          ·
            refine ⟨2178193388729288826479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1486980020039194505542997 2178193388729288826479)
            ·
              rfl

theorem cell23_1030810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 11].length) (baseStart_1030810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030810 prefixEnd_1030810 := by exact prefixLift 1030810
  have htrace : WordTrace (prefixWord ++ tailWord_1030810) baseStart_1030810 baseEnd_1030810 := by
    simpa [prefixWord, tailWord_1030810, baseEnd_1030810] using wordTrace_append hprefix tailTrace_1030810
  have hstable : (prefixWord ++ tailWord_1030810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030810).length < 2 ^ (prefixWord ++ tailWord_1030810).sum := by decide
  have hdescent : baseEnd_1030810 < baseStart_1030810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030814 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1030814 : Nat := 118140960795 + 1030814 * 2 ^ 59
def prefixEnd_1030814 : Nat := 4983230072969 + 3 ^ 40 * 1030814 * 2
def baseEnd_1030814 : Nat := 176434349127945056394793

theorem tailTrace_1030814 : CollatzResearch.WordTrace tailWord_1030814 prefixEnd_1030814 176434349127945056394793 := by
  unfold tailWord_1030814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699609410943050232541437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25064583525029601240220997 4699609410943050232541437)
  ·
    refine ⟨1762353529103643837203039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4699609410943050232541437 1762353529103643837203039)
    ·
      refine ⟨2643530293655465755804559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762353529103643837203039 2643530293655465755804559)
      ·
        refine ⟨3965295440483198633706839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643530293655465755804559 3965295440483198633706839)
        ·
          refine ⟨5947943160724797950560259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965295440483198633706839 5947943160724797950560259)
          ·
            refine ⟨8921914741087196925840389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947943160724797950560259 8921914741087196925840389)
            ·
              refine ⟨1672859013953849423595073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8921914741087196925840389 1672859013953849423595073)
              ·
                refine ⟨1254644260465387067696305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672859013953849423595073 1254644260465387067696305)
                ·
                  refine ⟨940983195349040300772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254644260465387067696305 940983195349040300772229)
                  ·
                    refine ⟨176434349127945056394793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 940983195349040300772229 176434349127945056394793)
                    ·
                      rfl

theorem cell23_1030814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1030814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030814 prefixEnd_1030814 := by exact prefixLift 1030814
  have htrace : WordTrace (prefixWord ++ tailWord_1030814) baseStart_1030814 baseEnd_1030814 := by
    simpa [prefixWord, tailWord_1030814, baseEnd_1030814] using wordTrace_append hprefix tailTrace_1030814
  have hstable : (prefixWord ++ tailWord_1030814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030814).length < 2 ^ (prefixWord ++ tailWord_1030814).sum := by decide
  have hdescent : baseEnd_1030814 < baseStart_1030814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030820 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1030820 : Nat := 118140960795 + 1030820 * 2 ^ 59
def prefixEnd_1030820 : Nat := 4983230072969 + 3 ^ 40 * 1030820 * 2
def baseEnd_1030820 : Nat := 529306128267762145709351

theorem tailTrace_1030820 : CollatzResearch.WordTrace tailWord_1030820 prefixEnd_1030820 529306128267762145709351 := by
  unfold tailWord_1030820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798547062761332442524957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25064729417015109923366609 18798547062761332442524957)
  ·
    refine ⟨7049455148535499665946859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18798547062761332442524957 7049455148535499665946859)
    ·
      refine ⟨10574182722803249498920289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7049455148535499665946859 10574182722803249498920289)
      ·
        refine ⟨7930637042102437124190217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10574182722803249498920289 7930637042102437124190217)
        ·
          refine ⟨5947977781576827843142663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930637042102437124190217 5947977781576827843142663)
          ·
            refine ⟨8921966672365241764713995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947977781576827843142663 8921966672365241764713995)
            ·
              refine ⟨13382950008547862647070993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921966672365241764713995 13382950008547862647070993)
              ·
                refine ⟨10037212506410896985303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382950008547862647070993 10037212506410896985303245)
                ·
                  refine ⟨3763954689904086369488717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10037212506410896985303245 3763954689904086369488717)
                  ·
                    refine ⟨1411483008714032388558269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763954689904086369488717 1411483008714032388558269)
                    ·
                      refine ⟨529306128267762145709351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411483008714032388558269 529306128267762145709351)
                      ·
                        rfl

theorem cell23_1030820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1030820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030820 prefixEnd_1030820 := by exact prefixLift 1030820
  have htrace : WordTrace (prefixWord ++ tailWord_1030820) baseStart_1030820 baseEnd_1030820 := by
    simpa [prefixWord, tailWord_1030820, baseEnd_1030820] using wordTrace_append hprefix tailTrace_1030820
  have hstable : (prefixWord ++ tailWord_1030820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030820).length < 2 ^ (prefixWord ++ tailWord_1030820).sum := by decide
  have hdescent : baseEnd_1030820 < baseStart_1030820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030837 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1030837 : Nat := 118140960795 + 1030837 * 2 ^ 59
def prefixEnd_1030837 : Nat := 4983230072969 + 3 ^ 40 * 1030837 * 2
def baseEnd_1030837 : Nat := 529314857438888579196773

theorem tailTrace_1030837 : CollatzResearch.WordTrace tailWord_1030837 prefixEnd_1030837 529314857438888579196773 := by
  unfold tailWord_1030837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37597714166461076788418765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25065142777640717858945843 37597714166461076788418765)
  ·
    refine ⟨14099142812422903795657037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37597714166461076788418765 14099142812422903795657037)
    ·
      refine ⟨5287178554658588923371389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14099142812422903795657037 5287178554658588923371389)
      ·
        refine ⟨1982691957996970846264271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5287178554658588923371389 1982691957996970846264271)
        ·
          refine ⟨2974037936995456269396407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982691957996970846264271 2974037936995456269396407)
          ·
            refine ⟨4461056905493184404094611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974037936995456269396407 4461056905493184404094611)
            ·
              refine ⟨6691585358239776606141917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461056905493184404094611 6691585358239776606141917)
              ·
                refine ⟨2509344509339916227303219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6691585358239776606141917 2509344509339916227303219)
                ·
                  refine ⟨3764016764009874340954829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509344509339916227303219 3764016764009874340954829)
                  ·
                    refine ⟨1411506286503702877858061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764016764009874340954829 1411506286503702877858061)
                    ·
                      refine ⟨529314857438888579196773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411506286503702877858061 529314857438888579196773)
                      ·
                        rfl

theorem cell23_1030837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1030837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030837 prefixEnd_1030837 := by exact prefixLift 1030837
  have htrace : WordTrace (prefixWord ++ tailWord_1030837) baseStart_1030837 baseEnd_1030837 := by
    simpa [prefixWord, tailWord_1030837, baseEnd_1030837] using wordTrace_append hprefix tailTrace_1030837
  have hstable : (prefixWord ++ tailWord_1030837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030837).length < 2 ^ (prefixWord ++ tailWord_1030837).sum := by decide
  have hdescent : baseEnd_1030837 < baseStart_1030837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030838 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1030838 : Nat := 118140960795 + 1030838 * 2 ^ 59
def prefixEnd_1030838 : Nat := 4983230072969 + 3 ^ 40 * 1030838 * 2
def baseEnd_1030838 : Nat := 529315370919543075284269

theorem tailTrace_1030838 : CollatzResearch.WordTrace tailWord_1030838 prefixEnd_1030838 529315370919543075284269 := by
  unfold tailWord_1030838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349859414966090872450323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25065167092971635972803445 2349859414966090872450323)
  ·
    refine ⟨3524789122449136308675485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349859414966090872450323 3524789122449136308675485)
    ·
      refine ⟨1321795920918426115753307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3524789122449136308675485 1321795920918426115753307)
      ·
        refine ⟨1982693881377639173629961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321795920918426115753307 1982693881377639173629961)
        ·
          refine ⟨1487020411033229380222471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982693881377639173629961 1487020411033229380222471)
          ·
            refine ⟨2230530616549844070333707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487020411033229380222471 2230530616549844070333707)
            ·
              refine ⟨3345795924824766105500561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230530616549844070333707 3345795924824766105500561)
              ·
                refine ⟨2509346943618574579125421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345795924824766105500561 2509346943618574579125421)
                ·
                  refine ⟨941005103856965467172033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2509346943618574579125421 941005103856965467172033)
                  ·
                    refine ⟨705753827892724100379025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 941005103856965467172033 705753827892724100379025)
                    ·
                      refine ⟨529315370919543075284269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705753827892724100379025 529315370919543075284269)
                      ·
                        rfl

theorem cell23_1030838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1030838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030838 prefixEnd_1030838 := by exact prefixLift 1030838
  have htrace : WordTrace (prefixWord ++ tailWord_1030838) baseStart_1030838 baseEnd_1030838 := by
    simpa [prefixWord, tailWord_1030838, baseEnd_1030838] using wordTrace_append hprefix tailTrace_1030838
  have hstable : (prefixWord ++ tailWord_1030838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030838).length < 2 ^ (prefixWord ++ tailWord_1030838).sum := by decide
  have hdescent : baseEnd_1030838 < baseStart_1030838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030847 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 3, 3, 2]
def baseStart_1030847 : Nat := 118140960795 + 1030847 * 2 ^ 59
def prefixEnd_1030847 : Nat := 4983230072969 + 3 ^ 40 * 1030847 * 2
def baseEnd_1030847 : Nat := 529319992245433540071727

theorem tailTrace_1030847 : CollatzResearch.WordTrace tailWord_1030847 prefixEnd_1030847 529319992245433540071727 := by
  unfold tailWord_1030847
  simp only [CollatzResearch.WordTrace]
  refine ⟨37598078896424848496282795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25065385930949898997521863 37598078896424848496282795)
  ·
    refine ⟨56397118344637272744424193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37598078896424848496282795 56397118344637272744424193)
    ·
      refine ⟨42297838758477954558318145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56397118344637272744424193 42297838758477954558318145)
      ·
        refine ⟨31723379068858465918738609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42297838758477954558318145 31723379068858465918738609)
        ·
          refine ⟨23792534301643849439053957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31723379068858465918738609 23792534301643849439053957)
          ·
            refine ⟨4461100181558221769822617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23792534301643849439053957 4461100181558221769822617)
            ·
              refine ⟨3345825136168666327366963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4461100181558221769822617 3345825136168666327366963)
              ·
                refine ⟨5018737704252999491050445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345825136168666327366963 5018737704252999491050445)
                ·
                  refine ⟨1882026639094874809143917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5018737704252999491050445 1882026639094874809143917)
                  ·
                    refine ⟨705759989660578053428969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882026639094874809143917 705759989660578053428969)
                    ·
                      refine ⟨529319992245433540071727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705759989660578053428969 529319992245433540071727)
                      ·
                        rfl

theorem cell23_1030847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_1030847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030847 prefixEnd_1030847 := by exact prefixLift 1030847
  have htrace : WordTrace (prefixWord ++ tailWord_1030847) baseStart_1030847 baseEnd_1030847 := by
    simpa [prefixWord, tailWord_1030847, baseEnd_1030847] using wordTrace_append hprefix tailTrace_1030847
  have hstable : (prefixWord ++ tailWord_1030847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030847).length < 2 ^ (prefixWord ++ tailWord_1030847).sum := by decide
  have hdescent : baseEnd_1030847 < baseStart_1030847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030853 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1030853 : Nat := 118140960795 + 1030853 * 2 ^ 59
def prefixEnd_1030853 : Nat := 4983230072969 + 3 ^ 40 * 1030853 * 2
def baseEnd_1030853 : Nat := 176441024376453505532233

theorem tailTrace_1030853 : CollatzResearch.WordTrace tailWord_1030853 prefixEnd_1030853 176441024376453505532233 := by
  unfold tailWord_1030853
  simp only [CollatzResearch.WordTrace]
  refine ⟨37598297734403111521001213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25065531822935407680667475 37598297734403111521001213)
  ·
    refine ⟨14099361650401166820375455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37598297734403111521001213 14099361650401166820375455)
    ·
      refine ⟨21149042475601750230563183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099361650401166820375455 21149042475601750230563183)
      ·
        refine ⟨31723563713402625345844775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21149042475601750230563183 31723563713402625345844775)
        ·
          refine ⟨47585345570103938018767163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31723563713402625345844775 47585345570103938018767163)
          ·
            refine ⟨71378018355155907028150745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47585345570103938018767163 71378018355155907028150745)
            ·
              refine ⟨53533513766366930271113059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71378018355155907028150745 53533513766366930271113059)
              ·
                refine ⟨80300270649550395406669589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53533513766366930271113059 80300270649550395406669589)
                ·
                  refine ⟨3764075186697674784687637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80300270649550395406669589 3764075186697674784687637)
                  ·
                    refine ⟨176441024376453505532233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3764075186697674784687637 176441024376453505532233)
                    ·
                      rfl

theorem cell23_1030853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1030853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030853 prefixEnd_1030853 := by exact prefixLift 1030853
  have htrace : WordTrace (prefixWord ++ tailWord_1030853) baseStart_1030853 baseEnd_1030853 := by
    simpa [prefixWord, tailWord_1030853, baseEnd_1030853] using wordTrace_append hprefix tailTrace_1030853
  have hstable : (prefixWord ++ tailWord_1030853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030853).length < 2 ^ (prefixWord ++ tailWord_1030853).sum := by decide
  have hdescent : baseEnd_1030853 < baseStart_1030853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030894 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1030894 : Nat := 118140960795 + 1030894 * 2 ^ 59
def prefixEnd_1030894 : Nat := 4983230072969 + 3 ^ 40 * 1030894 * 2
def baseEnd_1030894 : Nat := 529344125836194856184011

theorem tailTrace_1030894 : CollatzResearch.WordTrace tailWord_1030894 prefixEnd_1030894 529344125836194856184011 := by
  unfold tailWord_1030894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699974140906821940405467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25066528751503050348829157 4699974140906821940405467)
  ·
    refine ⟨7049961211360232910608201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699974140906821940405467 7049961211360232910608201)
    ·
      refine ⟨5287470908520174682956151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7049961211360232910608201 5287470908520174682956151)
      ·
        refine ⟨7931206362780262024434227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287470908520174682956151 7931206362780262024434227)
        ·
          refine ⟨11896809544170393036651341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931206362780262024434227 11896809544170393036651341)
          ·
            refine ⟨4461303579063897388744253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11896809544170393036651341 4461303579063897388744253)
            ·
              refine ⟨1672988842148961520779095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461303579063897388744253 1672988842148961520779095)
              ·
                refine ⟨2509483263223442281168643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672988842148961520779095 2509483263223442281168643)
                ·
                  refine ⟨3764224894835163421752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509483263223442281168643 3764224894835163421752965)
                  ·
                    refine ⟨705792167781593141578681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764224894835163421752965 705792167781593141578681)
                    ·
                      refine ⟨529344125836194856184011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705792167781593141578681 529344125836194856184011)
                      ·
                        rfl

theorem cell23_1030894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1030894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030894 prefixEnd_1030894 := by exact prefixLift 1030894
  have htrace : WordTrace (prefixWord ++ tailWord_1030894) baseStart_1030894 baseEnd_1030894 := by
    simpa [prefixWord, tailWord_1030894, baseEnd_1030894] using wordTrace_append hprefix tailTrace_1030894
  have hstable : (prefixWord ++ tailWord_1030894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030894).length < 2 ^ (prefixWord ++ tailWord_1030894).sum := by decide
  have hdescent : baseEnd_1030894 < baseStart_1030894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030940 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1030940 : Nat := 118140960795 + 1030940 * 2 ^ 59
def prefixEnd_1030940 : Nat := 4983230072969 + 3 ^ 40 * 1030940 * 2
def baseEnd_1030940 : Nat := 529367745946301676208799

theorem tailTrace_1030940 : CollatzResearch.WordTrace tailWord_1030940 prefixEnd_1030940 529367745946301676208799 := by
  unfold tailWord_1030940
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800735442543962689709137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25067647256725283586278849 18800735442543962689709137)
  ·
    refine ⟨14100551581907972017281853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18800735442543962689709137 14100551581907972017281853)
    ·
      refine ⟨5287706843215489506480695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14100551581907972017281853 5287706843215489506480695)
      ·
        refine ⟨7931560264823234259721043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287706843215489506480695 7931560264823234259721043)
        ·
          refine ⟨11897340397234851389581565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931560264823234259721043 11897340397234851389581565)
          ·
            refine ⟨4461502648963069271093087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11897340397234851389581565 4461502648963069271093087)
            ·
              refine ⟨6692253973444603906639631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461502648963069271093087 6692253973444603906639631)
              ·
                refine ⟨10038380960166905859959447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692253973444603906639631 10038380960166905859959447)
                ·
                  refine ⟨15057571440250358789939171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10038380960166905859959447 15057571440250358789939171)
                  ·
                    refine ⟨22586357160375538184908757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15057571440250358789939171 22586357160375538184908757)
                    ·
                      refine ⟨529367745946301676208799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22586357160375538184908757 529367745946301676208799)
                      ·
                        rfl

theorem cell23_1030940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1030940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030940 prefixEnd_1030940 := by exact prefixLift 1030940
  have htrace : WordTrace (prefixWord ++ tailWord_1030940) baseStart_1030940 baseEnd_1030940 := by
    simpa [prefixWord, tailWord_1030940, baseEnd_1030940] using wordTrace_append hprefix tailTrace_1030940
  have hstable : (prefixWord ++ tailWord_1030940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030940).length < 2 ^ (prefixWord ++ tailWord_1030940).sum := by decide
  have hdescent : baseEnd_1030940 < baseStart_1030940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030967 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1030967 : Nat := 118140960795 + 1030967 * 2 ^ 59
def prefixEnd_1030967 : Nat := 4983230072969 + 3 ^ 40 * 1030967 * 2
def baseEnd_1030967 : Nat := 529381609923973070571175

theorem tailTrace_1030967 : CollatzResearch.WordTrace tailWord_1030967 prefixEnd_1030967 529381609923973070571175 := by
  unfold tailWord_1030967
  simp only [CollatzResearch.WordTrace]
  refine ⟨37602455655990108990651155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25068303770660072660434103 37602455655990108990651155)
  ·
    refine ⟨56403683483985163485976733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37602455655990108990651155 56403683483985163485976733)
    ·
      refine ⟨21151381306494436307241275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56403683483985163485976733 21151381306494436307241275)
      ·
        refine ⟨31727071959741654460861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21151381306494436307241275 31727071959741654460861913)
        ·
          refine ⟨23795303969806240845646435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31727071959741654460861913 23795303969806240845646435)
          ·
            refine ⟨35692955954709361268469653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795303969806240845646435 35692955954709361268469653)
            ·
              refine ⟨1673107310377001309459515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35692955954709361268469653 1673107310377001309459515)
              ·
                refine ⟨2509660965565501964189273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673107310377001309459515 2509660965565501964189273)
                ·
                  refine ⟨1882245724174126473141955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2509660965565501964189273 1882245724174126473141955)
                  ·
                    refine ⟨2823368586261189709712933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882245724174126473141955 2823368586261189709712933)
                    ·
                      refine ⟨529381609923973070571175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2823368586261189709712933 529381609923973070571175)
                      ·
                        rfl

theorem cell23_1030967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1030967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030967 prefixEnd_1030967 := by exact prefixLift 1030967
  have htrace : WordTrace (prefixWord ++ tailWord_1030967) baseStart_1030967 baseEnd_1030967 := by
    simpa [prefixWord, tailWord_1030967, baseEnd_1030967] using wordTrace_append hprefix tailTrace_1030967
  have hstable : (prefixWord ++ tailWord_1030967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030967).length < 2 ^ (prefixWord ++ tailWord_1030967).sum := by decide
  have hdescent : baseEnd_1030967 < baseStart_1030967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030990 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_1030990 : Nat := 118140960795 + 1030990 * 2 ^ 59
def prefixEnd_1030990 : Nat := 4983230072969 + 3 ^ 40 * 1030990 * 2
def baseEnd_1030990 : Nat := 58821491108780720064841

theorem tailTrace_1030990 : CollatzResearch.WordTrace tailWord_1030990 prefixEnd_1030990 58821491108780720064841 := by
  unfold tailWord_1030990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700411816863347989842303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25068863023271189279158949 4700411816863347989842303)
  ·
    refine ⟨7050617725295021984763455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4700411816863347989842303 7050617725295021984763455)
    ·
      refine ⟨10575926587942532977145183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7050617725295021984763455 10575926587942532977145183)
      ·
        refine ⟨15863889881913799465717775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575926587942532977145183 15863889881913799465717775)
        ·
          refine ⟨23795834822870699198576663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15863889881913799465717775 23795834822870699198576663)
          ·
            refine ⟨35693752234306048797864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795834822870699198576663 35693752234306048797864995)
            ·
              refine ⟨53540628351459073196797493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35693752234306048797864995 53540628351459073196797493)
              ·
                refine ⟨5019433907949288112199765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53540628351459073196797493 5019433907949288112199765)
                ·
                  refine ⟨58821491108780720064841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5019433907949288112199765 58821491108780720064841)
                  ·
                    rfl

theorem cell23_1030990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_1030990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1030990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1030990 prefixEnd_1030990 := by exact prefixLift 1030990
  have htrace : WordTrace (prefixWord ++ tailWord_1030990) baseStart_1030990 baseEnd_1030990 := by
    simpa [prefixWord, tailWord_1030990, baseEnd_1030990] using wordTrace_append hprefix tailTrace_1030990
  have hstable : (prefixWord ++ tailWord_1030990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030990).length < 2 ^ (prefixWord ++ tailWord_1030990).sum := by decide
  have hdescent : baseEnd_1030990 < baseStart_1030990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031044 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_1031044 : Nat := 118140960795 + 1031044 * 2 ^ 59
def prefixEnd_1031044 : Nat := 4983230072969 + 3 ^ 40 * 1031044 * 2
def baseEnd_1031044 : Nat := 529421147934369269308321

theorem tailTrace_1031044 : CollatzResearch.WordTrace tailWord_1031044 prefixEnd_1031044 529421147934369269308321 := by
  unfold tailWord_1031044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18802632038355575570602093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25070176051140767427469457 18802632038355575570602093)
  ·
    refine ⟨7050987014383340838975785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18802632038355575570602093 7050987014383340838975785)
    ·
      refine ⟨5288240260787505629231839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7050987014383340838975785 5288240260787505629231839)
      ·
        refine ⟨7932360391181258443847759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288240260787505629231839 7932360391181258443847759)
        ·
          refine ⟨11898540586771887665771639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7932360391181258443847759 11898540586771887665771639)
          ·
            refine ⟨17847810880157831498657459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898540586771887665771639 17847810880157831498657459)
            ·
              refine ⟨26771716320236747247986189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847810880157831498657459 26771716320236747247986189)
              ·
                refine ⟨10039393620088780217994821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26771716320236747247986189 10039393620088780217994821)
                ·
                  refine ⟨1882386303766646290874029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10039393620088780217994821 1882386303766646290874029)
                  ·
                    refine ⟨705894863912492359077761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882386303766646290874029 705894863912492359077761)
                    ·
                      refine ⟨529421147934369269308321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 705894863912492359077761 529421147934369269308321)
                      ·
                        rfl

theorem cell23_1031044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_1031044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031044 prefixEnd_1031044 := by exact prefixLift 1031044
  have htrace : WordTrace (prefixWord ++ tailWord_1031044) baseStart_1031044 baseEnd_1031044 := by
    simpa [prefixWord, tailWord_1031044, baseEnd_1031044] using wordTrace_append hprefix tailTrace_1031044
  have hstable : (prefixWord ++ tailWord_1031044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031044).length < 2 ^ (prefixWord ++ tailWord_1031044).sum := by decide
  have hdescent : baseEnd_1031044 < baseStart_1031044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031051 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 1, 1, 3]
def baseStart_1031051 : Nat := 118140960795 + 1031051 * 2 ^ 59
def prefixEnd_1031051 : Nat := 4983230072969 + 3 ^ 40 * 1031051 * 2
def baseEnd_1031051 : Nat := 529424742298950741920789

theorem tailTrace_1031051 : CollatzResearch.WordTrace tailWord_1031051 prefixEnd_1031051 529424742298950741920789 := by
  unfold tailWord_1031051
  simp only [CollatzResearch.WordTrace]
  refine ⟨37605519387685791336709007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25070346258457194224472671 37605519387685791336709007)
  ·
    refine ⟨56408279081528687005063511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37605519387685791336709007 56408279081528687005063511)
    ·
      refine ⟨84612418622293030507595267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56408279081528687005063511 84612418622293030507595267)
      ·
        refine ⟨126918627933439545761392901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84612418622293030507595267 126918627933439545761392901)
        ·
          refine ⟨23797242737519914830261169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126918627933439545761392901 23797242737519914830261169)
          ·
            refine ⟨17847932053139936122695877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23797242737519914830261169 17847932053139936122695877)
            ·
              refine ⟨3346487259963738023005477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17847932053139936122695877 3346487259963738023005477)
              ·
                refine ⟨627466361243200879313527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3346487259963738023005477 627466361243200879313527)
                ·
                  refine ⟨941199541864801318970291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627466361243200879313527 941199541864801318970291)
                  ·
                    refine ⟨1411799312797201978455437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 941199541864801318970291 1411799312797201978455437)
                    ·
                      refine ⟨529424742298950741920789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411799312797201978455437 529424742298950741920789)
                      ·
                        rfl

theorem cell23_1031051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 1, 3].length) (baseStart_1031051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031051 prefixEnd_1031051 := by exact prefixLift 1031051
  have htrace : WordTrace (prefixWord ++ tailWord_1031051) baseStart_1031051 baseEnd_1031051 := by
    simpa [prefixWord, tailWord_1031051, baseEnd_1031051] using wordTrace_append hprefix tailTrace_1031051
  have hstable : (prefixWord ++ tailWord_1031051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031051).length < 2 ^ (prefixWord ++ tailWord_1031051).sum := by decide
  have hdescent : baseEnd_1031051 < baseStart_1031051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031097 : List Nat := [1, 2, 1, 4, 2, 4, 9]
def baseStart_1031097 : Nat := 118140960795 + 1031097 * 2 ^ 59
def prefixEnd_1031097 : Nat := 4983230072969 + 3 ^ 40 * 1031097 * 2
def baseEnd_1031097 : Nat := 6536399535914290888217

theorem tailTrace_1031097 : CollatzResearch.WordTrace tailWord_1031097 prefixEnd_1031097 6536399535914290888217 := by
  unfold tailWord_1031097
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607197145519141192883545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25071464763679427461922363 37607197145519141192883545)
  ·
    refine ⟨28205397859139355894662659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37607197145519141192883545 28205397859139355894662659)
    ·
      refine ⟨42308096788709033841993989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28205397859139355894662659 42308096788709033841993989)
      ·
        refine ⟨7932768147882943845373873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42308096788709033841993989 7932768147882943845373873)
        ·
          refine ⟨5949576110912207884030405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932768147882943845373873 5949576110912207884030405)
          ·
            refine ⟨1115545520796038978255701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5949576110912207884030405 1115545520796038978255701)
            ·
              refine ⟨6536399535914290888217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1115545520796038978255701 6536399535914290888217)
              ·
                rfl

theorem cell23_1031097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 9].length) (baseStart_1031097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031097 prefixEnd_1031097 := by exact prefixLift 1031097
  have htrace : WordTrace (prefixWord ++ tailWord_1031097) baseStart_1031097 baseEnd_1031097 := by
    simpa [prefixWord, tailWord_1031097, baseEnd_1031097] using wordTrace_append hprefix tailTrace_1031097
  have hstable : (prefixWord ++ tailWord_1031097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031097).length < 2 ^ (prefixWord ++ tailWord_1031097).sum := by decide
  have hdescent : baseEnd_1031097 < baseStart_1031097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3]
def baseStart_1031107 : Nat := 118140960795 + 1031107 * 2 ^ 59
def prefixEnd_1031107 : Nat := 4983230072969 + 3 ^ 40 * 1031107 * 2
def baseEnd_1031107 : Nat := 529453497215602522820531

theorem tailTrace_1031107 : CollatzResearch.WordTrace tailWord_1031107 prefixEnd_1031107 529453497215602522820531 := by
  unfold tailWord_1031107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607561875482912900747575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25071707916988608600498383 37607561875482912900747575)
  ·
    refine ⟨56411342813224369351121363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37607561875482912900747575 56411342813224369351121363)
    ·
      refine ⟨84617014219836554026682045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56411342813224369351121363 84617014219836554026682045)
      ·
        refine ⟨31731380332438707760005767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84617014219836554026682045 31731380332438707760005767)
        ·
          refine ⟨47597070498658061640008651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731380332438707760005767 47597070498658061640008651)
          ·
            refine ⟨71395605747987092460012977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47597070498658061640008651 71395605747987092460012977)
            ·
              refine ⟨53546704310990319345009733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71395605747987092460012977 53546704310990319345009733)
              ·
                refine ⟨10040007058310684877189325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53546704310990319345009733 10040007058310684877189325)
                ·
                  refine ⟨3765002646866506828945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10040007058310684877189325 3765002646866506828945997)
                  ·
                    refine ⟨1411875992574940060854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3765002646866506828945997 1411875992574940060854749)
                    ·
                      refine ⟨529453497215602522820531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411875992574940060854749 529453497215602522820531)
                      ·
                        rfl

theorem cell23_1031107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_1031107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031107 prefixEnd_1031107 := by exact prefixLift 1031107
  have htrace : WordTrace (prefixWord ++ tailWord_1031107) baseStart_1031107 baseEnd_1031107 := by
    simpa [prefixWord, tailWord_1031107, baseEnd_1031107] using wordTrace_append hprefix tailTrace_1031107
  have hstable : (prefixWord ++ tailWord_1031107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031107).length < 2 ^ (prefixWord ++ tailWord_1031107).sum := by decide
  have hdescent : baseEnd_1031107 < baseStart_1031107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031118 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1031118 : Nat := 118140960795 + 1031118 * 2 ^ 59
def prefixEnd_1031118 : Nat := 4983230072969 + 3 ^ 40 * 1031118 * 2
def baseEnd_1031118 : Nat := 176486381834267326594327

theorem tailTrace_1031118 : CollatzResearch.WordTrace tailWord_1031118 prefixEnd_1031118 176486381834267326594327 := by
  unfold tailWord_1031118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700995384805382722424751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25071975385628707852932005 4700995384805382722424751)
  ·
    refine ⟨7051493077208074083637127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4700995384805382722424751 7051493077208074083637127)
    ·
      refine ⟨10577239615812111125455691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051493077208074083637127 10577239615812111125455691)
      ·
        refine ⟨15865859423718166688183537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10577239615812111125455691 15865859423718166688183537)
        ·
          refine ⟨11899394567788625016137653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15865859423718166688183537 11899394567788625016137653)
          ·
            refine ⟨1115568240730183595262905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11899394567788625016137653 1115568240730183595262905)
            ·
              refine ⟨836676180547637696447179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115568240730183595262905 836676180547637696447179)
              ·
                refine ⟨1255014270821456544670769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836676180547637696447179 1255014270821456544670769)
                ·
                  refine ⟨941260703116092408503077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255014270821456544670769 941260703116092408503077)
                  ·
                    refine ⟨176486381834267326594327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941260703116092408503077 176486381834267326594327)
                    ·
                      rfl

theorem cell23_1031118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1031118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031118 prefixEnd_1031118 := by exact prefixLift 1031118
  have htrace : WordTrace (prefixWord ++ tailWord_1031118) baseStart_1031118 baseEnd_1031118 := by
    simpa [prefixWord, tailWord_1031118, baseEnd_1031118] using wordTrace_append hprefix tailTrace_1031118
  have hstable : (prefixWord ++ tailWord_1031118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031118).length < 2 ^ (prefixWord ++ tailWord_1031118).sum := by decide
  have hdescent : baseEnd_1031118 < baseStart_1031118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031158 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1031158 : Nat := 118140960795 + 1031158 * 2 ^ 59
def prefixEnd_1031158 : Nat := 4983230072969 + 3 ^ 40 * 1031158 * 2
def baseEnd_1031158 : Nat := 529479684728981823282797

theorem tailTrace_1031158 : CollatzResearch.WordTrace tailWord_1031158 prefixEnd_1031158 529479684728981823282797 := by
  unfold tailWord_1031158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350588874893634288178383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25072947998865432407236085 2350588874893634288178383)
  ·
    refine ⟨3525883312340451432267575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2350588874893634288178383 3525883312340451432267575)
    ·
      refine ⟨5288824968510677148401363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525883312340451432267575 5288824968510677148401363)
      ·
        refine ⟨7933237452766015722602045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288824968510677148401363 7933237452766015722602045)
        ·
          refine ⟨2974964044787255895975767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7933237452766015722602045 2974964044787255895975767)
          ·
            refine ⟨4462446067180883843963651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974964044787255895975767 4462446067180883843963651)
            ·
              refine ⟨6693669100771325765945477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462446067180883843963651 6693669100771325765945477)
              ·
                refine ⟨1255062956394623581114777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6693669100771325765945477 1255062956394623581114777)
                ·
                  refine ⟨941297217295967685836083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255062956394623581114777 941297217295967685836083)
                  ·
                    refine ⟨1411945825943951528754125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 941297217295967685836083 1411945825943951528754125)
                    ·
                      refine ⟨529479684728981823282797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1411945825943951528754125 529479684728981823282797)
                      ·
                        rfl

theorem cell23_1031158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1031158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031158 prefixEnd_1031158 := by exact prefixLift 1031158
  have htrace : WordTrace (prefixWord ++ tailWord_1031158) baseStart_1031158 baseEnd_1031158 := by
    simpa [prefixWord, tailWord_1031158, baseEnd_1031158] using wordTrace_append hprefix tailTrace_1031158
  have hstable : (prefixWord ++ tailWord_1031158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031158).length < 2 ^ (prefixWord ++ tailWord_1031158).sum := by decide
  have hdescent : baseEnd_1031158 < baseStart_1031158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031271 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1031271 : Nat := 118140960795 + 1031271 * 2 ^ 59
def prefixEnd_1031271 : Nat := 4983230072969 + 3 ^ 40 * 1031271 * 2
def baseEnd_1031271 : Nat := 529537708042939881169777

theorem tailTrace_1031271 : CollatzResearch.WordTrace tailWord_1031271 prefixEnd_1031271 529537708042939881169777 := by
  unfold tailWord_1031271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37613543446888768909717667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25075695631259179273145111 37613543446888768909717667)
  ·
    refine ⟨56420315170333153364576501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37613543446888768909717667 56420315170333153364576501)
    ·
      refine ⟨5289404547218733127929047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56420315170333153364576501 5289404547218733127929047)
      ·
        refine ⟨7934106820828099691893571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5289404547218733127929047 7934106820828099691893571)
        ·
          refine ⟨11901160231242149537840357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934106820828099691893571 11901160231242149537840357)
          ·
            refine ⟨2231467543357903038345067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11901160231242149537840357 2231467543357903038345067)
            ·
              refine ⟨3347201315036854557517601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231467543357903038345067 3347201315036854557517601)
              ·
                refine ⟨2510400986277640918138201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347201315036854557517601 2510400986277640918138201)
                ·
                  refine ⟨1882800739708230688603651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2510400986277640918138201 1882800739708230688603651)
                  ·
                    refine ⟨2824201109562346032905477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882800739708230688603651 2824201109562346032905477)
                    ·
                      refine ⟨529537708042939881169777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2824201109562346032905477 529537708042939881169777)
                      ·
                        rfl

theorem cell23_1031271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1031271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031271 prefixEnd_1031271 := by exact prefixLift 1031271
  have htrace : WordTrace (prefixWord ++ tailWord_1031271) baseStart_1031271 baseEnd_1031271 := by
    simpa [prefixWord, tailWord_1031271, baseEnd_1031271] using wordTrace_append hprefix tailTrace_1031271
  have hstable : (prefixWord ++ tailWord_1031271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031271).length < 2 ^ (prefixWord ++ tailWord_1031271).sum := by decide
  have hdescent : baseEnd_1031271 < baseStart_1031271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031332 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1031332 : Nat := 118140960795 + 1031332 * 2 ^ 59
def prefixEnd_1031332 : Nat := 4983230072969 + 3 ^ 40 * 1031332 * 2
def baseEnd_1031332 : Nat := 176523010120954714168999

theorem tailTrace_1031332 : CollatzResearch.WordTrace tailWord_1031332 prefixEnd_1031332 176523010120954714168999 := by
  unfold tailWord_1031332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807884149833888163844125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25077178866445184218458833 18807884149833888163844125)
  ·
    refine ⟨7052956556187708061441547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18807884149833888163844125 7052956556187708061441547)
    ·
      refine ⟨10579434834281562092162321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052956556187708061441547 10579434834281562092162321)
      ·
        refine ⟨7934576125711171569121741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10579434834281562092162321 7934576125711171569121741)
        ·
          refine ⟨2975466047141689338420653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7934576125711171569121741 2975466047141689338420653)
          ·
            refine ⟨1115799767678133501907745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2975466047141689338420653 1115799767678133501907745)
            ·
              refine ⟨836849825758600126430809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115799767678133501907745 836849825758600126430809)
              ·
                refine ⟨627637369318950094823107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836849825758600126430809 627637369318950094823107)
                ·
                  refine ⟨941456053978425142234661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627637369318950094823107 941456053978425142234661)
                  ·
                    refine ⟨176523010120954714168999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941456053978425142234661 176523010120954714168999)
                    ·
                      rfl

theorem cell23_1031332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1031332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031332 prefixEnd_1031332 := by exact prefixLift 1031332
  have htrace : WordTrace (prefixWord ++ tailWord_1031332) baseStart_1031332 baseEnd_1031332 := by
    simpa [prefixWord, tailWord_1031332, baseEnd_1031332] using wordTrace_append hprefix tailTrace_1031332
  have hstable : (prefixWord ++ tailWord_1031332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031332).length < 2 ^ (prefixWord ++ tailWord_1031332).sum := by decide
  have hdescent : baseEnd_1031332 < baseStart_1031332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031366 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1031366 : Nat := 118140960795 + 1031366 * 2 ^ 59
def prefixEnd_1031366 : Nat := 4983230072969 + 3 ^ 40 * 1031366 * 2
def baseEnd_1031366 : Nat := 176528829568372336493947

theorem tailTrace_1031366 : CollatzResearch.WordTrace tailWord_1031366 prefixEnd_1031366 176528829568372336493947 := by
  unfold tailWord_1031366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175531511923268754200811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25078005587696400089617301 1175531511923268754200811)
  ·
    refine ⟨1763297267884903131301217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175531511923268754200811 1763297267884903131301217)
    ·
      refine ⟨1322472950913677348475913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763297267884903131301217 1322472950913677348475913)
      ·
        refine ⟨991854713185258011356935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322472950913677348475913 991854713185258011356935)
        ·
          refine ⟨1487782069777887017035403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991854713185258011356935 1487782069777887017035403)
          ·
            refine ⟨2231673104666830525553105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487782069777887017035403 2231673104666830525553105)
            ·
              refine ⟨1673754828500122894164829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231673104666830525553105 1673754828500122894164829)
              ·
                refine ⟨627658060687546085311811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673754828500122894164829 627658060687546085311811)
                ·
                  refine ⟨941487091031319127967717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627658060687546085311811 941487091031319127967717)
                  ·
                    refine ⟨176528829568372336493947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941487091031319127967717 176528829568372336493947)
                    ·
                      rfl

theorem cell23_1031366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1031366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031366 prefixEnd_1031366 := by exact prefixLift 1031366
  have htrace : WordTrace (prefixWord ++ tailWord_1031366) baseStart_1031366 baseEnd_1031366 := by
    simpa [prefixWord, tailWord_1031366, baseEnd_1031366] using wordTrace_append hprefix tailTrace_1031366
  have hstable : (prefixWord ++ tailWord_1031366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031366).length < 2 ^ (prefixWord ++ tailWord_1031366).sum := by decide
  have hdescent : baseEnd_1031366 < baseStart_1031366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031378 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1031378 : Nat := 118140960795 + 1031378 * 2 ^ 59
def prefixEnd_1031378 : Nat := 4983230072969 + 3 ^ 40 * 1031378 * 2
def baseEnd_1031378 : Nat := 529592650472970962531785

theorem tailTrace_1031378 : CollatzResearch.WordTrace tailWord_1031378 prefixEnd_1031378 529592650472970962531785 := by
  unfold tailWord_1031378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404361514375281545965697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25078297371667417455908525 9404361514375281545965697)
  ·
    refine ⟨7053271135781461159474273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9404361514375281545965697 7053271135781461159474273)
    ·
      refine ⟨5289953351836095869605705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7053271135781461159474273 5289953351836095869605705)
      ·
        refine ⟨3967465013877071902204279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5289953351836095869605705 3967465013877071902204279)
        ·
          refine ⟨5951197520815607853306419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967465013877071902204279 5951197520815607853306419)
          ·
            refine ⟨8926796281223411779959629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951197520815607853306419 8926796281223411779959629)
            ·
              refine ⟨3347548605458779417484861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8926796281223411779959629 3347548605458779417484861)
              ·
                refine ⟨1255330727047042281556823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3347548605458779417484861 1255330727047042281556823)
                ·
                  refine ⟨1882996090570563422335235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255330727047042281556823 1882996090570563422335235)
                  ·
                    refine ⟨2824494135855845133502853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882996090570563422335235 2824494135855845133502853)
                    ·
                      refine ⟨529592650472970962531785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2824494135855845133502853 529592650472970962531785)
                      ·
                        rfl

theorem cell23_1031378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1031378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031378 prefixEnd_1031378 := by exact prefixLift 1031378
  have htrace : WordTrace (prefixWord ++ tailWord_1031378) baseStart_1031378 baseEnd_1031378 := by
    simpa [prefixWord, tailWord_1031378, baseEnd_1031378] using wordTrace_append hprefix tailTrace_1031378
  have hstable : (prefixWord ++ tailWord_1031378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031378).length < 2 ^ (prefixWord ++ tailWord_1031378).sum := by decide
  have hdescent : baseEnd_1031378 < baseStart_1031378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031468 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_1031468 : Nat := 118140960795 + 1031468 * 2 ^ 59
def prefixEnd_1031468 : Nat := 4983230072969 + 3 ^ 40 * 1031468 * 2
def baseEnd_1031468 : Nat := 529638863731875610406371

theorem tailTrace_1031468 : CollatzResearch.WordTrace tailWord_1031468 prefixEnd_1031468 529638863731875610406371 := by
  unfold tailWord_1031468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810364313587535777319529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25080485751450047703092705 18810364313587535777319529)
  ·
    refine ⟨14107773235190651832989647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18810364313587535777319529 14107773235190651832989647)
    ·
      refine ⟨21161659852785977749484471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107773235190651832989647 21161659852785977749484471)
      ·
        refine ⟨31742489779178966624226707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21161659852785977749484471 31742489779178966624226707)
        ·
          refine ⟨47613734668768449936340061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31742489779178966624226707 47613734668768449936340061)
          ·
            refine ⟨17855150500788168726127523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47613734668768449936340061 17855150500788168726127523)
            ·
              refine ⟨26782725751182253089191285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855150500788168726127523 26782725751182253089191285)
              ·
                refine ⟨2510880539173336227111683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26782725751182253089191285 2510880539173336227111683)
                ·
                  refine ⟨3766320808760004340667525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510880539173336227111683 3766320808760004340667525)
                  ·
                    refine ⟨706185151642500813875161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766320808760004340667525 706185151642500813875161)
                    ·
                      refine ⟨529638863731875610406371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706185151642500813875161 529638863731875610406371)
                      ·
                        rfl

theorem cell23_1031468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_1031468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031468 prefixEnd_1031468 := by exact prefixLift 1031468
  have htrace : WordTrace (prefixWord ++ tailWord_1031468) baseStart_1031468 baseEnd_1031468 := by
    simpa [prefixWord, tailWord_1031468, baseEnd_1031468] using wordTrace_append hprefix tailTrace_1031468
  have hstable : (prefixWord ++ tailWord_1031468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031468).length < 2 ^ (prefixWord ++ tailWord_1031468).sum := by decide
  have hdescent : baseEnd_1031468 < baseStart_1031468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031489 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1031489 : Nat := 118140960795 + 1031489 * 2 ^ 59
def prefixEnd_1031489 : Nat := 4983230072969 + 3 ^ 40 * 1031489 * 2
def baseEnd_1031489 : Nat := 529649646825620028243775

theorem tailTrace_1031489 : CollatzResearch.WordTrace tailWord_1031489 prefixEnd_1031489 529649646825620028243775 := by
  unfold tailWord_1031489
  simp only [CollatzResearch.WordTrace]
  refine ⟨37621494560098992141153521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25080996373399328094102347 37621494560098992141153521)
  ·
    refine ⟨28216120920074244105865141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37621494560098992141153521 28216120920074244105865141)
    ·
      refine ⟨2645261336256960384924857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28216120920074244105865141 2645261336256960384924857)
      ·
        refine ⟨1983946002192720288693643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645261336256960384924857 1983946002192720288693643)
        ·
          refine ⟨2975919003289080433040465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983946002192720288693643 2975919003289080433040465)
          ·
            refine ⟨2231939252466810324780349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975919003289080433040465 2231939252466810324780349)
            ·
              refine ⟨836977219675053871792631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2231939252466810324780349 836977219675053871792631)
              ·
                refine ⟨1255465829512580807688947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836977219675053871792631 1255465829512580807688947)
                ·
                  refine ⟨1883198744268871211533421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255465829512580807688947 1883198744268871211533421)
                  ·
                    refine ⟨706199529100826704325033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883198744268871211533421 706199529100826704325033)
                    ·
                      refine ⟨529649646825620028243775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706199529100826704325033 529649646825620028243775)
                      ·
                        rfl

theorem cell23_1031489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1031489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031489 prefixEnd_1031489 := by exact prefixLift 1031489
  have htrace : WordTrace (prefixWord ++ tailWord_1031489) baseStart_1031489 baseEnd_1031489 := by
    simpa [prefixWord, tailWord_1031489, baseEnd_1031489] using wordTrace_append hprefix tailTrace_1031489
  have hstable : (prefixWord ++ tailWord_1031489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031489).length < 2 ^ (prefixWord ++ tailWord_1031489).sum := by decide
  have hdescent : baseEnd_1031489 < baseStart_1031489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031502 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_1031502 : Nat := 118140960795 + 1031502 * 2 ^ 59
def prefixEnd_1031502 : Nat := 4983230072969 + 3 ^ 40 * 1031502 * 2
def baseEnd_1031502 : Nat := 529656322074128477381215

theorem tailTrace_1031502 : CollatzResearch.WordTrace tailWord_1031502 prefixEnd_1031502 529656322074128477381215 := by
  unfold tailWord_1031502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702746088631486920172095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25081312472701263574251173 4702746088631486920172095)
  ·
    refine ⟨7054119132947230380258143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702746088631486920172095 7054119132947230380258143)
    ·
      refine ⟨10581178699420845570387215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054119132947230380258143 10581178699420845570387215)
      ·
        refine ⟨15871768049131268355580823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581178699420845570387215 15871768049131268355580823)
        ·
          refine ⟨23807652073696902533371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15871768049131268355580823 23807652073696902533371235)
          ·
            refine ⟨35711478110545353800056853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23807652073696902533371235 35711478110545353800056853)
            ·
              refine ⟨1673975536431813459377665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35711478110545353800056853 1673975536431813459377665)
              ·
                refine ⟨1255481652323860094533249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673975536431813459377665 1255481652323860094533249)
                ·
                  refine ⟨941611239242895070899937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255481652323860094533249 941611239242895070899937)
                  ·
                    refine ⟨706208429432171303174953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 941611239242895070899937 706208429432171303174953)
                    ·
                      refine ⟨529656322074128477381215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706208429432171303174953 529656322074128477381215)
                      ·
                        rfl

theorem cell23_1031502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_1031502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031502 prefixEnd_1031502 := by exact prefixLift 1031502
  have htrace : WordTrace (prefixWord ++ tailWord_1031502) baseStart_1031502 baseEnd_1031502 := by
    simpa [prefixWord, tailWord_1031502, baseEnd_1031502] using wordTrace_append hprefix tailTrace_1031502
  have hstable : (prefixWord ++ tailWord_1031502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031502).length < 2 ^ (prefixWord ++ tailWord_1031502).sum := by decide
  have hdescent : baseEnd_1031502 < baseStart_1031502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031521 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1031521 : Nat := 118140960795 + 1031521 * 2 ^ 59
def prefixEnd_1031521 : Nat := 4983230072969 + 3 ^ 40 * 1031521 * 2
def baseEnd_1031521 : Nat := 176555359402187967681209

theorem tailTrace_1031521 : CollatzResearch.WordTrace tailWord_1031521 prefixEnd_1031521 176555359402187967681209 := by
  unfold tailWord_1031521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37622661695983061606318417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25081774463988707737545611 37622661695983061606318417)
  ·
    refine ⟨28216996271987296204738813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37622661695983061606318417 28216996271987296204738813)
    ·
      refine ⟨10581373601995236076777055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28216996271987296204738813 10581373601995236076777055)
      ·
        refine ⟨15872060402992854115165583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581373601995236076777055 15872060402992854115165583)
        ·
          refine ⟨23808090604489281172748375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15872060402992854115165583 23808090604489281172748375)
          ·
            refine ⟨35712135906733921759122563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23808090604489281172748375 35712135906733921759122563)
            ·
              refine ⟨53568203860100882638683845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35712135906733921759122563 53568203860100882638683845)
              ·
                refine ⟨10044038223768915494753221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53568203860100882638683845 10044038223768915494753221)
                ·
                  refine ⟨1883257166956671655266229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10044038223768915494753221 1883257166956671655266229)
                  ·
                    refine ⟨176555359402187967681209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1883257166956671655266229 176555359402187967681209)
                    ·
                      rfl

theorem cell23_1031521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1031521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031521 prefixEnd_1031521 := by exact prefixLift 1031521
  have htrace : WordTrace (prefixWord ++ tailWord_1031521) baseStart_1031521 baseEnd_1031521 := by
    simpa [prefixWord, tailWord_1031521, baseEnd_1031521] using wordTrace_append hprefix tailTrace_1031521
  have hstable : (prefixWord ++ tailWord_1031521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031521).length < 2 ^ (prefixWord ++ tailWord_1031521).sum := by decide
  have hdescent : baseEnd_1031521 < baseStart_1031521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031578 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1031578 : Nat := 118140960795 + 1031578 * 2 ^ 59
def prefixEnd_1031578 : Nat := 4983230072969 + 3 ^ 40 * 1031578 * 2
def baseEnd_1031578 : Nat := 529695346603870180030865

theorem tailTrace_1031578 : CollatzResearch.WordTrace tailWord_1031578 prefixEnd_1031578 529695346603870180030865 := by
  unfold tailWord_1031578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406185164194140085285847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25083160437851040227428925 9406185164194140085285847)
  ·
    refine ⟨14109277746291210127928771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9406185164194140085285847 14109277746291210127928771)
    ·
      refine ⟨21163916619436815191893157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109277746291210127928771 21163916619436815191893157)
      ·
        refine ⟨3968234366144402848479967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21163916619436815191893157 3968234366144402848479967)
        ·
          refine ⟨5952351549216604272719951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968234366144402848479967 5952351549216604272719951)
          ·
            refine ⟨8928527323824906409079927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952351549216604272719951 8928527323824906409079927)
            ·
              refine ⟨13392790985737359613619891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928527323824906409079927 13392790985737359613619891)
              ·
                refine ⟨20089186478606039420429837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392790985737359613619891 20089186478606039420429837)
                ·
                  refine ⟨7533444929477264782661189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20089186478606039420429837 7533444929477264782661189)
                  ·
                    refine ⟨1412520924276987146748973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533444929477264782661189 1412520924276987146748973)
                    ·
                      refine ⟨529695346603870180030865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1412520924276987146748973 529695346603870180030865)
                      ·
                        rfl

theorem cell23_1031578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1031578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031578 prefixEnd_1031578 := by exact prefixLift 1031578
  have htrace : WordTrace (prefixWord ++ tailWord_1031578) baseStart_1031578 baseEnd_1031578 := by
    simpa [prefixWord, tailWord_1031578, baseEnd_1031578] using wordTrace_append hprefix tailTrace_1031578
  have hstable : (prefixWord ++ tailWord_1031578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031578).length < 2 ^ (prefixWord ++ tailWord_1031578).sum := by decide
  have hdescent : baseEnd_1031578 < baseStart_1031578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031612 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1031612 : Nat := 118140960795 + 1031612 * 2 ^ 59
def prefixEnd_1031612 : Nat := 4983230072969 + 3 ^ 40 * 1031612 * 2
def baseEnd_1031612 : Nat := 529712804946123047005709

theorem tailTrace_1031612 : CollatzResearch.WordTrace tailWord_1031612 prefixEnd_1031612 529712804946123047005709 := by
  unfold tailWord_1031612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812990369326692073940545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25083987159102256098587393 18812990369326692073940545)
  ·
    refine ⟨14109742776995019055455409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812990369326692073940545 14109742776995019055455409)
    ·
      refine ⟨10582307082746264291591557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14109742776995019055455409 10582307082746264291591557)
      ·
        refine ⟨1984182578014924554673417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10582307082746264291591557 1984182578014924554673417)
        ·
          refine ⟨1488136933511193416005063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984182578014924554673417 1488136933511193416005063)
          ·
            refine ⟨2232205400266790124007595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488136933511193416005063 2232205400266790124007595)
            ·
              refine ⟨3348308100400185186011393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232205400266790124007595 3348308100400185186011393)
              ·
                refine ⟨2511231075300138889508545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348308100400185186011393 2511231075300138889508545)
                ·
                  refine ⟨1883423306475104167131409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511231075300138889508545 1883423306475104167131409)
                  ·
                    refine ⟨1412567479856328125348557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883423306475104167131409 1412567479856328125348557)
                    ·
                      refine ⟨529712804946123047005709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1412567479856328125348557 529712804946123047005709)
                      ·
                        rfl

theorem cell23_1031612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1031612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031612 prefixEnd_1031612 := by exact prefixLift 1031612
  have htrace : WordTrace (prefixWord ++ tailWord_1031612) baseStart_1031612 baseEnd_1031612 := by
    simpa [prefixWord, tailWord_1031612, baseEnd_1031612] using wordTrace_append hprefix tailTrace_1031612
  have hstable : (prefixWord ++ tailWord_1031612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031612).length < 2 ^ (prefixWord ++ tailWord_1031612).sum := by decide
  have hdescent : baseEnd_1031612 < baseStart_1031612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031645 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1031645 : Nat := 118140960795 + 1031645 * 2 ^ 59
def prefixEnd_1031645 : Nat := 4983230072969 + 3 ^ 40 * 1031645 * 2
def baseEnd_1031645 : Nat := 176576583269240472631019

theorem tailTrace_1031645 : CollatzResearch.WordTrace tailWord_1031645 prefixEnd_1031645 176576583269240472631019 := by
  unfold tailWord_1031645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37627184347533830783832389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25084789565022553855888259 37627184347533830783832389)
  ·
    refine ⟨7055097065162593271968573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37627184347533830783832389 7055097065162593271968573)
    ·
      refine ⟨2645661399435972476988215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7055097065162593271968573 2645661399435972476988215)
      ·
        refine ⟨3968492099153958715482323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645661399435972476988215 3968492099153958715482323)
        ·
          refine ⟨5952738148730938073223485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968492099153958715482323 5952738148730938073223485)
          ·
            refine ⟨2232276805774101777458807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5952738148730938073223485 2232276805774101777458807)
            ·
              refine ⟨3348415208661152666188211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232276805774101777458807 3348415208661152666188211)
              ·
                refine ⟨5022622812991728999282317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348415208661152666188211 5022622812991728999282317)
                ·
                  refine ⟨1883483554871898374730869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5022622812991728999282317 1883483554871898374730869)
                  ·
                    refine ⟨176576583269240472631019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1883483554871898374730869 176576583269240472631019)
                    ·
                      rfl

theorem cell23_1031645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1031645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031645 prefixEnd_1031645 := by exact prefixLift 1031645
  have htrace : WordTrace (prefixWord ++ tailWord_1031645) baseStart_1031645 baseEnd_1031645 := by
    simpa [prefixWord, tailWord_1031645, baseEnd_1031645] using wordTrace_append hprefix tailTrace_1031645
  have hstable : (prefixWord ++ tailWord_1031645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031645).length < 2 ^ (prefixWord ++ tailWord_1031645).sum := by decide
  have hdescent : baseEnd_1031645 < baseStart_1031645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031662 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1031662 : Nat := 118140960795 + 1031662 * 2 ^ 59
def prefixEnd_1031662 : Nat := 4983230072969 + 3 ^ 40 * 1031662 * 2
def baseEnd_1031662 : Nat := 176579492992949283793493

theorem tailTrace_1031662 : CollatzResearch.WordTrace tailWord_1031662 prefixEnd_1031662 176579492992949283793493 := by
  unfold tailWord_1031662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703475548559030335900155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25085202925648161791467493 4703475548559030335900155)
  ·
    refine ⟨7055213322838545503850233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703475548559030335900155 7055213322838545503850233)
    ·
      refine ⟨5291409992128909127887675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055213322838545503850233 5291409992128909127887675)
      ·
        refine ⟨7937114988193363691831513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291409992128909127887675 7937114988193363691831513)
        ·
          refine ⟨5952836241145022768873635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937114988193363691831513 5952836241145022768873635)
          ·
            refine ⟨8929254361717534153310453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952836241145022768873635 8929254361717534153310453)
            ·
              refine ⟨837117596411018826872855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8929254361717534153310453 837117596411018826872855)
              ·
                refine ⟨1255676394616528240309283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837117596411018826872855 1255676394616528240309283)
                ·
                  refine ⟨1883514591924792360463925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255676394616528240309283 1883514591924792360463925)
                  ·
                    refine ⟨176579492992949283793493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1883514591924792360463925 176579492992949283793493)
                    ·
                      rfl

theorem cell23_1031662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1031662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031662 prefixEnd_1031662 := by exact prefixLift 1031662
  have htrace : WordTrace (prefixWord ++ tailWord_1031662) baseStart_1031662 baseEnd_1031662 := by
    simpa [prefixWord, tailWord_1031662, baseEnd_1031662] using wordTrace_append hprefix tailTrace_1031662
  have hstable : (prefixWord ++ tailWord_1031662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031662).length < 2 ^ (prefixWord ++ tailWord_1031662).sum := by decide
  have hdescent : baseEnd_1031662 < baseStart_1031662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031669 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1031669 : Nat := 118140960795 + 1031669 * 2 ^ 59
def prefixEnd_1031669 : Nat := 4983230072969 + 3 ^ 40 * 1031669 * 2
def baseEnd_1031669 : Nat := 529742073343429323992947

theorem tailTrace_1031669 : CollatzResearch.WordTrace tailWord_1031669 prefixEnd_1031669 529742073343429323992947 := by
  unfold tailWord_1031669
  simp only [CollatzResearch.WordTrace]
  refine ⟨37628059699446882882706061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25085373132964588588470707 37628059699446882882706061)
  ·
    refine ⟨14110522387292581081014773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37628059699446882882706061 14110522387292581081014773)
    ·
      refine ⟨1322861473808679476345135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14110522387292581081014773 1322861473808679476345135)
      ·
        refine ⟨1984292210713019214517703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322861473808679476345135 1984292210713019214517703)
        ·
          refine ⟨2976438316069528821776555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984292210713019214517703 2976438316069528821776555)
          ·
            refine ⟨4464657474104293232664833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976438316069528821776555 4464657474104293232664833)
            ·
              refine ⟨3348493105578219924498625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464657474104293232664833 3348493105578219924498625)
              ·
                refine ⟨2511369829183664943373969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348493105578219924498625 2511369829183664943373969)
                ·
                  refine ⟨1883527371887748707530477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511369829183664943373969 1883527371887748707530477)
                  ·
                    refine ⟨706322764457905765323929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883527371887748707530477 706322764457905765323929)
                    ·
                      refine ⟨529742073343429323992947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706322764457905765323929 529742073343429323992947)
                      ·
                        rfl

theorem cell23_1031669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1031669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031669 prefixEnd_1031669 := by exact prefixLift 1031669
  have htrace : WordTrace (prefixWord ++ tailWord_1031669) baseStart_1031669 baseEnd_1031669 := by
    simpa [prefixWord, tailWord_1031669, baseEnd_1031669] using wordTrace_append hprefix tailTrace_1031669
  have hstable : (prefixWord ++ tailWord_1031669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031669).length < 2 ^ (prefixWord ++ tailWord_1031669).sum := by decide
  have hdescent : baseEnd_1031669 < baseStart_1031669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031682 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1031682 : Nat := 118140960795 + 1031682 * 2 ^ 59
def prefixEnd_1031682 : Nat := 4983230072969 + 3 ^ 40 * 1031682 * 2
def baseEnd_1031682 : Nat := 529748748591937773130387

theorem tailTrace_1031682 : CollatzResearch.WordTrace tailWord_1031682 prefixEnd_1031682 529748748591937773130387 := by
  unfold tailWord_1031682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407133462099946525732325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25085689232266524068619533 9407133462099946525732325)
  ·
    refine ⟨1763837524143739973574811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9407133462099946525732325 1763837524143739973574811)
    ·
      refine ⟨2645756286215609960362217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763837524143739973574811 2645756286215609960362217)
      ·
        refine ⟨1984317214661707470271663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645756286215609960362217 1984317214661707470271663)
        ·
          refine ⟨2976475821992561205407495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984317214661707470271663 2976475821992561205407495)
          ·
            refine ⟨4464713732988841808111243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976475821992561205407495 4464713732988841808111243)
            ·
              refine ⟨6697070599483262712166865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464713732988841808111243 6697070599483262712166865)
              ·
                refine ⟨5022802949612447034125149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697070599483262712166865 5022802949612447034125149)
                ·
                  refine ⟨1883551106104667637796931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5022802949612447034125149 1883551106104667637796931)
                  ·
                    refine ⟨2825326659157001456695397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1883551106104667637796931 2825326659157001456695397)
                    ·
                      refine ⟨529748748591937773130387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2825326659157001456695397 529748748591937773130387)
                      ·
                        rfl

theorem cell23_1031682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1031682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031682 prefixEnd_1031682 := by exact prefixLift 1031682
  have htrace : WordTrace (prefixWord ++ tailWord_1031682) baseStart_1031682 baseEnd_1031682 := by
    simpa [prefixWord, tailWord_1031682, baseEnd_1031682] using wordTrace_append hprefix tailTrace_1031682
  have hstable : (prefixWord ++ tailWord_1031682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031682).length < 2 ^ (prefixWord ++ tailWord_1031682).sum := by decide
  have hdescent : baseEnd_1031682 < baseStart_1031682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031688 : List Nat := [2, 1, 3, 2, 1, 1, 5, 8]
def baseStart_1031688 : Nat := 118140960795 + 1031688 * 2 ^ 59
def prefixEnd_1031688 : Nat := 4983230072969 + 3 ^ 40 * 1031688 * 2
def baseEnd_1031688 : Nat := 19620438128735731468717

theorem tailTrace_1031688 : CollatzResearch.WordTrace tailWord_1031688 prefixEnd_1031688 19620438128735731468717 := by
  unfold tailWord_1031688
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814376343189024563823859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25085835124252032751765145 18814376343189024563823859)
  ·
    refine ⟨28221564514783536845735789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18814376343189024563823859 28221564514783536845735789)
    ·
      refine ⟨10583086693043826317150921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28221564514783536845735789 10583086693043826317150921)
      ·
        refine ⟨7937315019782869737863191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10583086693043826317150921 7937315019782869737863191)
        ·
          refine ⟨11905972529674304606794787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937315019782869737863191 11905972529674304606794787)
          ·
            refine ⟨17858958794511456910192181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905972529674304606794787 17858958794511456910192181)
            ·
              refine ⟨1674277386985449085330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17858958794511456910192181 1674277386985449085330517)
              ·
                refine ⟨19620438128735731468717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1674277386985449085330517 19620438128735731468717)
                ·
                  rfl

theorem cell23_1031688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 8].length) (baseStart_1031688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031688 prefixEnd_1031688 := by exact prefixLift 1031688
  have htrace : WordTrace (prefixWord ++ tailWord_1031688) baseStart_1031688 baseEnd_1031688 := by
    simpa [prefixWord, tailWord_1031688, baseEnd_1031688] using wordTrace_append hprefix tailTrace_1031688
  have hstable : (prefixWord ++ tailWord_1031688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031688).length < 2 ^ (prefixWord ++ tailWord_1031688).sum := by decide
  have hdescent : baseEnd_1031688 < baseStart_1031688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031749 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_1031749 : Nat := 118140960795 + 1031749 * 2 ^ 59
def prefixEnd_1031749 : Nat := 4983230072969 + 3 ^ 40 * 1031749 * 2
def baseEnd_1031749 : Nat := 529783151795789010992579

theorem tailTrace_1031749 : CollatzResearch.WordTrace tailWord_1031749 prefixEnd_1031749 529783151795789010992579 := by
  unfold tailWord_1031749
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630977539157056545618301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25087318359438037697078867 37630977539157056545618301)
  ·
    refine ⟨14111616577183896204606863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37630977539157056545618301 14111616577183896204606863)
    ·
      refine ⟨21167424865775844306910295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111616577183896204606863 21167424865775844306910295)
      ·
        refine ⟨31751137298663766460365443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167424865775844306910295 31751137298663766460365443)
        ·
          refine ⟨47626705947995649690548165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31751137298663766460365443 47626705947995649690548165)
          ·
            refine ⟨8930007365249184316977781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47626705947995649690548165 8930007365249184316977781)
            ·
              refine ⟨837188190492111029716667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8930007365249184316977781 837188190492111029716667)
              ·
                refine ⟨1255782285738166544575001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837188190492111029716667 1255782285738166544575001)
                ·
                  refine ⟨941836714303624908431251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255782285738166544575001 941836714303624908431251)
                  ·
                    refine ⟨1412755071455437362646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 941836714303624908431251 1412755071455437362646877)
                    ·
                      refine ⟨529783151795789010992579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1412755071455437362646877 529783151795789010992579)
                      ·
                        rfl

theorem cell23_1031749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_1031749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031749 prefixEnd_1031749 := by exact prefixLift 1031749
  have htrace : WordTrace (prefixWord ++ tailWord_1031749) baseStart_1031749 baseEnd_1031749 := by
    simpa [prefixWord, tailWord_1031749, baseEnd_1031749] using wordTrace_append hprefix tailTrace_1031749
  have hstable : (prefixWord ++ tailWord_1031749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031749).length < 2 ^ (prefixWord ++ tailWord_1031749).sum := by decide
  have hdescent : baseEnd_1031749 < baseStart_1031749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031788 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1031788 : Nat := 118140960795 + 1031788 * 2 ^ 59
def prefixEnd_1031788 : Nat := 4983230072969 + 3 ^ 40 * 1031788 * 2
def baseEnd_1031788 : Nat := 529803177541314358404899

theorem tailTrace_1031788 : CollatzResearch.WordTrace tailWord_1031788 prefixEnd_1031788 529803177541314358404899 := by
  unfold tailWord_1031788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816199993007883103144009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25088266657343844137525345 18816199993007883103144009)
  ·
    refine ⟨14112149994755912327358007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18816199993007883103144009 14112149994755912327358007)
    ·
      refine ⟨21168224992133868491037011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14112149994755912327358007 21168224992133868491037011)
      ·
        refine ⟨31752337488200802736555517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21168224992133868491037011 31752337488200802736555517)
        ·
          refine ⟨11907126558075301026208319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31752337488200802736555517 11907126558075301026208319)
          ·
            refine ⟨17860689837112951539312479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11907126558075301026208319 17860689837112951539312479)
            ·
              refine ⟨26791034755669427308968719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17860689837112951539312479 26791034755669427308968719)
              ·
                refine ⟨40186552133504140963453079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26791034755669427308968719 40186552133504140963453079)
                ·
                  refine ⟨60279828200256211445179619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40186552133504140963453079 60279828200256211445179619)
                  ·
                    refine ⟨90419742300384317167769429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60279828200256211445179619 90419742300384317167769429)
                    ·
                      refine ⟨529803177541314358404899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 90419742300384317167769429 529803177541314358404899)
                      ·
                        rfl

theorem cell23_1031788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1031788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031788 prefixEnd_1031788 := by exact prefixLift 1031788
  have htrace : WordTrace (prefixWord ++ tailWord_1031788) baseStart_1031788 baseEnd_1031788 := by
    simpa [prefixWord, tailWord_1031788, baseEnd_1031788] using wordTrace_append hprefix tailTrace_1031788
  have hstable : (prefixWord ++ tailWord_1031788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031788).length < 2 ^ (prefixWord ++ tailWord_1031788).sum := by decide
  have hdescent : baseEnd_1031788 < baseStart_1031788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031872 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_1031872 : Nat := 118140960795 + 1031872 * 2 ^ 59
def prefixEnd_1031872 : Nat := 4983230072969 + 3 ^ 40 * 1031872 * 2
def baseEnd_1031872 : Nat := 176615436638764009918171

theorem tailTrace_1031872 : CollatzResearch.WordTrace tailWord_1031872 prefixEnd_1031872 176615436638764009918171 := by
  unfold tailWord_1031872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817731858855724276172935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25090309145140965701563913 18817731858855724276172935)
  ·
    refine ⟨28226597788283586414259403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18817731858855724276172935 28226597788283586414259403)
    ·
      refine ⟨42339896682425379621389105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28226597788283586414259403 42339896682425379621389105)
      ·
        refine ⟨31754922511819034716041829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42339896682425379621389105 31754922511819034716041829)
        ·
          refine ⟨5954047970966069009257843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31754922511819034716041829 5954047970966069009257843)
          ·
            refine ⟨8931071956449103513886765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954047970966069009257843 8931071956449103513886765)
            ·
              refine ⟨3349151983668413817707537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8931071956449103513886765 3349151983668413817707537)
              ·
                refine ⟨2511863987751310363280653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349151983668413817707537 2511863987751310363280653)
                ·
                  refine ⟨941948995406741386230245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2511863987751310363280653 941948995406741386230245)
                  ·
                    refine ⟨176615436638764009918171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941948995406741386230245 176615436638764009918171)
                    ·
                      rfl

theorem cell23_1031872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_1031872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031872 prefixEnd_1031872 := by exact prefixLift 1031872
  have htrace : WordTrace (prefixWord ++ tailWord_1031872) baseStart_1031872 baseEnd_1031872 := by
    simpa [prefixWord, tailWord_1031872, baseEnd_1031872] using wordTrace_append hprefix tailTrace_1031872
  have hstable : (prefixWord ++ tailWord_1031872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031872).length < 2 ^ (prefixWord ++ tailWord_1031872).sum := by decide
  have hdescent : baseEnd_1031872 < baseStart_1031872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031889 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1031889 : Nat := 118140960795 + 1031889 * 2 ^ 59
def prefixEnd_1031889 : Nat := 4983230072969 + 3 ^ 40 * 1031889 * 2
def baseEnd_1031889 : Nat := 176618346362472821080645

theorem tailTrace_1031889 : CollatzResearch.WordTrace tailWord_1031889 prefixEnd_1031889 176618346362472821080645 := by
  unfold tailWord_1031889
  simp only [CollatzResearch.WordTrace]
  refine ⟨37636083758649860455714721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25090722505766573637143147 37636083758649860455714721)
  ·
    refine ⟨28227062818987395341786041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37636083758649860455714721 28227062818987395341786041)
    ·
      refine ⟨21170297114240546506339531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28227062818987395341786041 21170297114240546506339531)
      ·
        refine ⟨31755445671360819759509297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21170297114240546506339531 31755445671360819759509297)
        ·
          refine ⟨23816584253520614819631973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31755445671360819759509297 23816584253520614819631973)
          ·
            refine ⟨4465609547535115278680995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23816584253520614819631973 4465609547535115278680995)
            ·
              refine ⟨6698414321302672918021493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465609547535115278680995 6698414321302672918021493)
              ·
                refine ⟨627976342622125586064515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6698414321302672918021493 627976342622125586064515)
                ·
                  refine ⟨941964513933188379096773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627976342622125586064515 941964513933188379096773)
                  ·
                    refine ⟨176618346362472821080645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 941964513933188379096773 176618346362472821080645)
                    ·
                      rfl

theorem cell23_1031889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1031889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031889 prefixEnd_1031889 := by exact prefixLift 1031889
  have htrace : WordTrace (prefixWord ++ tailWord_1031889) baseStart_1031889 baseEnd_1031889 := by
    simpa [prefixWord, tailWord_1031889, baseEnd_1031889] using wordTrace_append hprefix tailTrace_1031889
  have hstable : (prefixWord ++ tailWord_1031889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031889).length < 2 ^ (prefixWord ++ tailWord_1031889).sum := by decide
  have hdescent : baseEnd_1031889 < baseStart_1031889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031892 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1031892 : Nat := 118140960795 + 1031892 * 2 ^ 59
def prefixEnd_1031892 : Nat := 4983230072969 + 3 ^ 40 * 1031892 * 2
def baseEnd_1031892 : Nat := 529856579529381951504421

theorem tailTrace_1031892 : CollatzResearch.WordTrace tailWord_1031892 prefixEnd_1031892 529856579529381951504421 := by
  unfold tailWord_1031892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818096588819495984036965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25090795451759327978715953 18818096588819495984036965)
  ·
    refine ⟨3528393110403655497006931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18818096588819495984036965 3528393110403655497006931)
    ·
      refine ⟨5292589665605483245510397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528393110403655497006931 5292589665605483245510397)
      ·
        refine ⟨1984721124602056217066399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5292589665605483245510397 1984721124602056217066399)
        ·
          refine ⟨2977081686903084325599599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984721124602056217066399 2977081686903084325599599)
          ·
            refine ⟨4465622530354626488399399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977081686903084325599599 4465622530354626488399399)
            ·
              refine ⟨6698433795531939732599099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465622530354626488399399 6698433795531939732599099)
              ·
                refine ⟨10047650693297909598898649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698433795531939732599099 10047650693297909598898649)
                ·
                  refine ⟨7535738019973432199173987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10047650693297909598898649 7535738019973432199173987)
                  ·
                    refine ⟨11303607029960148298760981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535738019973432199173987 11303607029960148298760981)
                    ·
                      refine ⟨529856579529381951504421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11303607029960148298760981 529856579529381951504421)
                      ·
                        rfl

theorem cell23_1031892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1031892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031892 prefixEnd_1031892 := by exact prefixLift 1031892
  have htrace : WordTrace (prefixWord ++ tailWord_1031892) baseStart_1031892 baseEnd_1031892 := by
    simpa [prefixWord, tailWord_1031892, baseEnd_1031892] using wordTrace_append hprefix tailTrace_1031892
  have hstable : (prefixWord ++ tailWord_1031892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031892).length < 2 ^ (prefixWord ++ tailWord_1031892).sum := by decide
  have hdescent : baseEnd_1031892 < baseStart_1031892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031915 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 5, 5]
def baseStart_1031915 : Nat := 118140960795 + 1031915 * 2 ^ 59
def prefixEnd_1031915 : Nat := 4983230072969 + 3 ^ 40 * 1031915 * 2
def baseEnd_1031915 : Nat := 176622796528145120505605

theorem tailTrace_1031915 : CollatzResearch.WordTrace tailWord_1031915 prefixEnd_1031915 176622796528145120505605 := by
  unfold tailWord_1031915
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637032056555666896161199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091354704370444597440799 37637032056555666896161199)
  ·
    refine ⟨56455548084833500344241799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637032056555666896161199 56455548084833500344241799)
    ·
      refine ⟨84683322127250250516362699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56455548084833500344241799 84683322127250250516362699)
      ·
        refine ⟨127024983190875375774544049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84683322127250250516362699 127024983190875375774544049)
        ·
          refine ⟨95268737393156531830908037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127024983190875375774544049 95268737393156531830908037)
          ·
            refine ⟨17862888261216849718295257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95268737393156531830908037 17862888261216849718295257)
            ·
              refine ⟨13397166195912637288721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17862888261216849718295257 13397166195912637288721443)
              ·
                refine ⟨20095749293868955933082165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397166195912637288721443 20095749293868955933082165)
                ·
                  refine ⟨1883976496300214618726453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20095749293868955933082165 1883976496300214618726453)
                  ·
                    refine ⟨176622796528145120505605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1883976496300214618726453 176622796528145120505605)
                    ·
                      rfl

theorem cell23_1031915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].length) (baseStart_1031915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031915 prefixEnd_1031915 := by exact prefixLift 1031915
  have htrace : WordTrace (prefixWord ++ tailWord_1031915) baseStart_1031915 baseEnd_1031915 := by
    simpa [prefixWord, tailWord_1031915, baseEnd_1031915] using wordTrace_append hprefix tailTrace_1031915
  have hstable : (prefixWord ++ tailWord_1031915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031915).length < 2 ^ (prefixWord ++ tailWord_1031915).sum := by decide
  have hdescent : baseEnd_1031915 < baseStart_1031915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031945 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_1031945 : Nat := 118140960795 + 1031945 * 2 ^ 59
def prefixEnd_1031945 : Nat := 4983230072969 + 3 ^ 40 * 1031945 * 2
def baseEnd_1031945 : Nat := 176627931334690081380559

theorem tailTrace_1031945 : CollatzResearch.WordTrace tailWord_1031945 prefixEnd_1031945 176627931334690081380559 := by
  unfold tailWord_1031945
  simp only [CollatzResearch.WordTrace]
  refine ⟨37638126246446982019753289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25092084164297988013168859 37638126246446982019753289)
  ·
    refine ⟨28228594684835236514814967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37638126246446982019753289 28228594684835236514814967)
    ·
      refine ⟨42342892027252854772222451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28228594684835236514814967 42342892027252854772222451)
      ·
        refine ⟨63514338040879282158333677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42342892027252854772222451 63514338040879282158333677)
        ·
          refine ⟨23817876765329730809375129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63514338040879282158333677 23817876765329730809375129)
          ·
            refine ⟨17863407573997298107031347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23817876765329730809375129 17863407573997298107031347)
            ·
              refine ⟨26795111360995947160547021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863407573997298107031347 26795111360995947160547021)
              ·
                refine ⟨10048166760373480185205133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26795111360995947160547021 10048166760373480185205133)
                ·
                  refine ⟨3768062535140055069451925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10048166760373480185205133 3768062535140055069451925)
                  ·
                    refine ⟨176627931334690081380559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3768062535140055069451925 176627931334690081380559)
                    ·
                      rfl

theorem cell23_1031945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_1031945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031945 prefixEnd_1031945 := by exact prefixLift 1031945
  have htrace : WordTrace (prefixWord ++ tailWord_1031945) baseStart_1031945 baseEnd_1031945 := by
    simpa [prefixWord, tailWord_1031945, baseEnd_1031945] using wordTrace_append hprefix tailTrace_1031945
  have hstable : (prefixWord ++ tailWord_1031945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031945).length < 2 ^ (prefixWord ++ tailWord_1031945).sum := by decide
  have hdescent : baseEnd_1031945 < baseStart_1031945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031986 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1031986 : Nat := 118140960795 + 1031986 * 2 ^ 59
def prefixEnd_1031986 : Nat := 4983230072969 + 3 ^ 40 * 1031986 * 2
def baseEnd_1031986 : Nat := 529904846710904583728989

theorem tailTrace_1031986 : CollatzResearch.WordTrace tailWord_1031986 prefixEnd_1031986 529904846710904583728989 := by
  unfold tailWord_1031986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409905409824611505498953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25093081092865630681330541 9409905409824611505498953)
  ·
    refine ⟨7057429057368458629124215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9409905409824611505498953 7057429057368458629124215)
    ·
      refine ⟨10586143586052687943686323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057429057368458629124215 10586143586052687943686323)
      ·
        refine ⟨15879215379079031915529485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586143586052687943686323 15879215379079031915529485)
        ·
          refine ⟨5954705767154636968323557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15879215379079031915529485 5954705767154636968323557)
          ·
            refine ⟨1116507331341494431560667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5954705767154636968323557 1116507331341494431560667)
            ·
              refine ⟨1674760997012241647341001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116507331341494431560667 1674760997012241647341001)
              ·
                refine ⟨1256070747759181235505751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674760997012241647341001 1256070747759181235505751)
                ·
                  refine ⟨1884106121638771853258627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256070747759181235505751 1884106121638771853258627)
                  ·
                    refine ⟨2826159182458157779887941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1884106121638771853258627 2826159182458157779887941)
                    ·
                      refine ⟨529904846710904583728989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2826159182458157779887941 529904846710904583728989)
                      ·
                        rfl

theorem cell23_1031986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1031986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031986 prefixEnd_1031986 := by exact prefixLift 1031986
  have htrace : WordTrace (prefixWord ++ tailWord_1031986) baseStart_1031986 baseEnd_1031986 := by
    simpa [prefixWord, tailWord_1031986, baseEnd_1031986] using wordTrace_append hprefix tailTrace_1031986
  have hstable : (prefixWord ++ tailWord_1031986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031986).length < 2 ^ (prefixWord ++ tailWord_1031986).sum := by decide
  have hdescent : baseEnd_1031986 < baseStart_1031986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031999 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_1031999 : Nat := 118140960795 + 1031999 * 2 ^ 59
def prefixEnd_1031999 : Nat := 4983230072969 + 3 ^ 40 * 1031999 * 2
def baseEnd_1031999 : Nat := 529911521959413032866429

theorem tailTrace_1031999 : CollatzResearch.WordTrace tailWord_1031999 prefixEnd_1031999 529911521959413032866429 := by
  unfold tailWord_1031999
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640095788251349242219051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25093397192167566161479367 37640095788251349242219051)
  ·
    refine ⟨56460143682377023863328577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37640095788251349242219051 56460143682377023863328577)
    ·
      refine ⟨42345107761782767897496433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56460143682377023863328577 42345107761782767897496433)
      ·
        refine ⟨31758830821337075923122325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42345107761782767897496433 31758830821337075923122325)
        ·
          refine ⟨1488695194750175433896359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31758830821337075923122325 1488695194750175433896359)
          ·
            refine ⟨2233042792125263150844539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488695194750175433896359 2233042792125263150844539)
            ·
              refine ⟨3349564188187894726266809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233042792125263150844539 3349564188187894726266809)
              ·
                refine ⟨2512173141140921044700107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349564188187894726266809 2512173141140921044700107)
                ·
                  refine ⟨3768259711711381567050161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512173141140921044700107 3768259711711381567050161)
                  ·
                    refine ⟨2826194783783536175287621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768259711711381567050161 2826194783783536175287621)
                    ·
                      refine ⟨529911521959413032866429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2826194783783536175287621 529911521959413032866429)
                      ·
                        rfl

theorem cell23_1031999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_1031999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1031999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1031999 prefixEnd_1031999 := by exact prefixLift 1031999
  have htrace : WordTrace (prefixWord ++ tailWord_1031999) baseStart_1031999 baseEnd_1031999 := by
    simpa [prefixWord, tailWord_1031999, baseEnd_1031999] using wordTrace_append hprefix tailTrace_1031999
  have hstable : (prefixWord ++ tailWord_1031999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031999).length < 2 ^ (prefixWord ++ tailWord_1031999).sum := by decide
  have hdescent : baseEnd_1031999 < baseStart_1031999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032013 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1032013 : Nat := 118140960795 + 1032013 * 2 ^ 59
def prefixEnd_1032013 : Nat := 4983230072969 + 3 ^ 40 * 1032013 * 2
def baseEnd_1032013 : Nat := 176639570229525326030455

theorem tailTrace_1032013 : CollatzResearch.WordTrace tailWord_1032013 prefixEnd_1032013 176639570229525326030455 := by
  unfold tailWord_1032013
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640606410200629633228693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25093737606800419755485795 37640606410200629633228693)
  ·
    refine ⟨1764403425478154514057595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37640606410200629633228693 1764403425478154514057595)
    ·
      refine ⟨2646605138217231771086393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764403425478154514057595 2646605138217231771086393)
      ·
        refine ⟨1984953853662923828314795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646605138217231771086393 1984953853662923828314795)
        ·
          refine ⟨2977430780494385742472193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984953853662923828314795 2977430780494385742472193)
          ·
            refine ⟨2233073085370789306854145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977430780494385742472193 2233073085370789306854145)
            ·
              refine ⟨1674804814028091980140609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233073085370789306854145 1674804814028091980140609)
              ·
                refine ⟨1256103610521068985105457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674804814028091980140609 1256103610521068985105457)
                ·
                  refine ⟨942077707890801738829093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1256103610521068985105457 942077707890801738829093)
                  ·
                    refine ⟨176639570229525326030455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942077707890801738829093 176639570229525326030455)
                    ·
                      rfl

theorem cell23_1032013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1032013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032013 prefixEnd_1032013 := by exact prefixLift 1032013
  have htrace : WordTrace (prefixWord ++ tailWord_1032013) baseStart_1032013 baseEnd_1032013 := by
    simpa [prefixWord, tailWord_1032013, baseEnd_1032013] using wordTrace_append hprefix tailTrace_1032013
  have hstable : (prefixWord ++ tailWord_1032013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032013).length < 2 ^ (prefixWord ++ tailWord_1032013).sum := by decide
  have hdescent : baseEnd_1032013 < baseStart_1032013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032015 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1032015 : Nat := 118140960795 + 1032015 * 2 ^ 59
def prefixEnd_1032015 : Nat := 4983230072969 + 3 ^ 40 * 1032015 * 2
def baseEnd_1032015 : Nat := 529919737649884970266355

theorem tailTrace_1032015 : CollatzResearch.WordTrace tailWord_1032015 prefixEnd_1032015 529919737649884970266355 := by
  unfold tailWord_1032015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640679356193383974801499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25093786237462255983200999 37640679356193383974801499)
  ·
    refine ⟨56461019034290075962202249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37640679356193383974801499 56461019034290075962202249)
    ·
      refine ⟨42345764275717556971651687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56461019034290075962202249 42345764275717556971651687)
      ·
        refine ⟨63518646413576335457477531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42345764275717556971651687 63518646413576335457477531)
        ·
          refine ⟨95277969620364503186216297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63518646413576335457477531 95277969620364503186216297)
          ·
            refine ⟨71458477215273377389662223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95277969620364503186216297 71458477215273377389662223)
            ·
              refine ⟨107187715822910066084493335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71458477215273377389662223 107187715822910066084493335)
              ·
                refine ⟨160781573734365099126740003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107187715822910066084493335 160781573734365099126740003)
                ·
                  refine ⟨241172360601547648690110005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160781573734365099126740003 241172360601547648690110005)
                  ·
                    refine ⟨22609908806395092064697813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241172360601547648690110005 22609908806395092064697813)
                    ·
                      refine ⟨529919737649884970266355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22609908806395092064697813 529919737649884970266355)
                      ·
                        rfl

theorem cell23_1032015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1032015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032015 prefixEnd_1032015 := by exact prefixLift 1032015
  have htrace : WordTrace (prefixWord ++ tailWord_1032015) baseStart_1032015 baseEnd_1032015 := by
    simpa [prefixWord, tailWord_1032015, baseEnd_1032015] using wordTrace_append hprefix tailTrace_1032015
  have hstable : (prefixWord ++ tailWord_1032015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032015).length < 2 ^ (prefixWord ++ tailWord_1032015).sum := by decide
  have hdescent : baseEnd_1032015 < baseStart_1032015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032020 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_1032020 : Nat := 118140960795 + 1032020 * 2 ^ 59
def prefixEnd_1032020 : Nat := 4983230072969 + 3 ^ 40 * 1032020 * 2
def baseEnd_1032020 : Nat := 529922305053157450703833

theorem tailTrace_1032020 : CollatzResearch.WordTrace tailWord_1032020 prefixEnd_1032020 529922305053157450703833 := by
  unfold tailWord_1032020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820430860587634914366757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25093907814116846552489009 18820430860587634914366757)
  ·
    refine ⟨3528830786360181546443767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18820430860587634914366757 3528830786360181546443767)
    ·
      refine ⟨5293246179540272319665651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528830786360181546443767 5293246179540272319665651)
      ·
        refine ⟨7939869269310408479498477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293246179540272319665651 7939869269310408479498477)
        ·
          refine ⟨2977450975991403179811929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7939869269310408479498477 2977450975991403179811929)
          ·
            refine ⟨2233088231993552384858947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977450975991403179811929 2233088231993552384858947)
            ·
              refine ⟨3349632347990328577288421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233088231993552384858947 3349632347990328577288421)
              ·
                refine ⟨628056065248186608241579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3349632347990328577288421 628056065248186608241579)
                ·
                  refine ⟨942084097872279912362369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628056065248186608241579 942084097872279912362369)
                  ·
                    refine ⟨706563073404209934271777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 942084097872279912362369 706563073404209934271777)
                    ·
                      refine ⟨529922305053157450703833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706563073404209934271777 529922305053157450703833)
                      ·
                        rfl

theorem cell23_1032020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_1032020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032020 prefixEnd_1032020 := by exact prefixLift 1032020
  have htrace : WordTrace (prefixWord ++ tailWord_1032020) baseStart_1032020 baseEnd_1032020 := by
    simpa [prefixWord, tailWord_1032020, baseEnd_1032020] using wordTrace_append hprefix tailTrace_1032020
  have hstable : (prefixWord ++ tailWord_1032020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032020).length < 2 ^ (prefixWord ++ tailWord_1032020).sum := by decide
  have hdescent : baseEnd_1032020 < baseStart_1032020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032036 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1032036 : Nat := 118140960795 + 1032036 * 2 ^ 59
def prefixEnd_1032036 : Nat := 4983230072969 + 3 ^ 40 * 1032036 * 2
def baseEnd_1032036 : Nat := 529930520743629388103759

theorem tailTrace_1032036 : CollatzResearch.WordTrace tailWord_1032036 prefixEnd_1032036 529930520743629388103759 := by
  unfold tailWord_1032036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820722644558652280657981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25094296859411536374210641 18820722644558652280657981)
  ·
    refine ⟨7057770991709494605246743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18820722644558652280657981 7057770991709494605246743)
    ·
      refine ⟨10586656487564241907870115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057770991709494605246743 10586656487564241907870115)
      ·
        refine ⟨15879984731346362861805173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586656487564241907870115 15879984731346362861805173)
        ·
          refine ⟨1488748568563721518294235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15879984731346362861805173 1488748568563721518294235)
          ·
            refine ⟨2233122852845582277441353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488748568563721518294235 2233122852845582277441353)
            ·
              refine ⟨1674842139634186708081015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233122852845582277441353 1674842139634186708081015)
              ·
                refine ⟨2512263209451280062121523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674842139634186708081015 2512263209451280062121523)
                ·
                  refine ⟨3768394814176920093182285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512263209451280062121523 3768394814176920093182285)
                  ·
                    refine ⟨1413148055316345034943357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768394814176920093182285 1413148055316345034943357)
                    ·
                      refine ⟨529930520743629388103759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1413148055316345034943357 529930520743629388103759)
                      ·
                        rfl

theorem cell23_1032036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1032036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032036 prefixEnd_1032036 := by exact prefixLift 1032036
  have htrace : WordTrace (prefixWord ++ tailWord_1032036) baseStart_1032036 baseEnd_1032036 := by
    simpa [prefixWord, tailWord_1032036, baseEnd_1032036] using wordTrace_append hprefix tailTrace_1032036
  have hstable : (prefixWord ++ tailWord_1032036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032036).length < 2 ^ (prefixWord ++ tailWord_1032036).sum := by decide
  have hdescent : baseEnd_1032036 < baseStart_1032036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032093 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1032093 : Nat := 118140960795 + 1032093 * 2 ^ 59
def prefixEnd_1032093 : Nat := 4983230072969 + 3 ^ 40 * 1032093 * 2
def baseEnd_1032093 : Nat := 529959789140935665090997

theorem tailTrace_1032093 : CollatzResearch.WordTrace tailWord_1032093 prefixEnd_1032093 529959789140935665090997 := by
  unfold tailWord_1032093
  simp only [CollatzResearch.WordTrace]
  refine ⟨37643524249910803296140933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25095682833273868864093955 37643524249910803296140933)
  ·
    refine ⟨7058160796858275618026425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37643524249910803296140933 7058160796858275618026425)
    ·
      refine ⟨5293620597643706713519819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7058160796858275618026425 5293620597643706713519819)
      ·
        refine ⟨7940430896465560070279729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293620597643706713519819 7940430896465560070279729)
        ·
          refine ⟨5955323172349170052709797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7940430896465560070279729 5955323172349170052709797)
          ·
            refine ⟨1116623094815469384883087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5955323172349170052709797 1116623094815469384883087)
            ·
              refine ⟨1674934642223204077324631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116623094815469384883087 1674934642223204077324631)
              ·
                refine ⟨2512401963334806115986947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674934642223204077324631 2512401963334806115986947)
                ·
                  refine ⟨3768602945002209173980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512401963334806115986947 3768602945002209173980421)
                  ·
                    refine ⟨706613052187914220121329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3768602945002209173980421 706613052187914220121329)
                    ·
                      refine ⟨529959789140935665090997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706613052187914220121329 529959789140935665090997)
                      ·
                        rfl

theorem cell23_1032093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1032093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032093 prefixEnd_1032093 := by exact prefixLift 1032093
  have htrace : WordTrace (prefixWord ++ tailWord_1032093) baseStart_1032093 baseEnd_1032093 := by
    simpa [prefixWord, tailWord_1032093, baseEnd_1032093] using wordTrace_append hprefix tailTrace_1032093
  have hstable : (prefixWord ++ tailWord_1032093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032093).length < 2 ^ (prefixWord ++ tailWord_1032093).sum := by decide
  have hdescent : baseEnd_1032093 < baseStart_1032093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032112 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_1032112 : Nat := 118140960795 + 1032112 * 2 ^ 59
def prefixEnd_1032112 : Nat := 4983230072969 + 3 ^ 40 * 1032112 * 2
def baseEnd_1032112 : Nat := 176656515091123696917803

theorem tailTrace_1032112 : CollatzResearch.WordTrace tailWord_1032112 prefixEnd_1032112 176656515091123696917803 := by
  unfold tailWord_1032112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18822108618420984770541295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25096144824561313027388393 18822108618420984770541295)
  ·
    refine ⟨28233162927631477155811943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18822108618420984770541295 28233162927631477155811943)
    ·
      refine ⟨42349744391447215733717915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28233162927631477155811943 42349744391447215733717915)
      ·
        refine ⟨63524616587170823600576873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42349744391447215733717915 63524616587170823600576873)
        ·
          refine ⟨47643462440378117700432655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63524616587170823600576873 47643462440378117700432655)
          ·
            refine ⟨71465193660567176550648983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47643462440378117700432655 71465193660567176550648983)
            ·
              refine ⟨107197790490850764825973475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71465193660567176550648983 107197790490850764825973475)
              ·
                refine ⟨160796685736276147238960213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107197790490850764825973475 160796685736276147238960213)
                ·
                  refine ⟨1884336160971986100456565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 160796685736276147238960213 1884336160971986100456565)
                  ·
                    refine ⟨176656515091123696917803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1884336160971986100456565 176656515091123696917803)
                    ·
                      rfl

theorem cell23_1032112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_1032112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032112 prefixEnd_1032112 := by exact prefixLift 1032112
  have htrace : WordTrace (prefixWord ++ tailWord_1032112) baseStart_1032112 baseEnd_1032112 := by
    simpa [prefixWord, tailWord_1032112, baseEnd_1032112] using wordTrace_append hprefix tailTrace_1032112
  have hstable : (prefixWord ++ tailWord_1032112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032112).length < 2 ^ (prefixWord ++ tailWord_1032112).sum := by decide
  have hdescent : baseEnd_1032112 < baseStart_1032112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032119 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_1032119 : Nat := 118140960795 + 1032119 * 2 ^ 59
def prefixEnd_1032119 : Nat := 4983230072969 + 3 ^ 40 * 1032119 * 2
def baseEnd_1032119 : Nat := 529973139637952563365877

theorem tailTrace_1032119 : CollatzResearch.WordTrace tailWord_1032119 prefixEnd_1032119 529973139637952563365877 := by
  unfold tailWord_1032119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37644472547816609736587411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25096315031877739824391607 37644472547816609736587411)
  ·
    refine ⟨56466708821724914604881117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37644472547816609736587411 56466708821724914604881117)
    ·
      refine ⟨21175015808146842976830419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56466708821724914604881117 21175015808146842976830419)
      ·
        refine ⟨31762523712220264465245629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175015808146842976830419 31762523712220264465245629)
        ·
          refine ⟨11910946392082599174467111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31762523712220264465245629 11910946392082599174467111)
          ·
            refine ⟨17866419588123898761700667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910946392082599174467111 17866419588123898761700667)
            ·
              refine ⟨26799629382185848142551001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17866419588123898761700667 26799629382185848142551001)
              ·
                refine ⟨20099722036639386106913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26799629382185848142551001 20099722036639386106913251)
                ·
                  refine ⟨30149583054959079160369877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20099722036639386106913251 30149583054959079160369877)
                  ·
                    refine ⟨706630852850603417821169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30149583054959079160369877 706630852850603417821169)
                    ·
                      refine ⟨529973139637952563365877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706630852850603417821169 529973139637952563365877)
                      ·
                        rfl

theorem cell23_1032119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_1032119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032119 prefixEnd_1032119 := by exact prefixLift 1032119
  have htrace : WordTrace (prefixWord ++ tailWord_1032119) baseStart_1032119 baseEnd_1032119 := by
    simpa [prefixWord, tailWord_1032119, baseEnd_1032119] using wordTrace_append hprefix tailTrace_1032119
  have hstable : (prefixWord ++ tailWord_1032119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032119).length < 2 ^ (prefixWord ++ tailWord_1032119).sum := by decide
  have hdescent : baseEnd_1032119 < baseStart_1032119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032172 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 10]
def baseStart_1032172 : Nat := 118140960795 + 1032172 * 2 ^ 59
def prefixEnd_1032172 : Nat := 4983230072969 + 3 ^ 40 * 1032172 * 2
def baseEnd_1032172 : Nat := 58888928234737872889237

theorem tailTrace_1032172 : CollatzResearch.WordTrace tailWord_1032172 prefixEnd_1032172 58888928234737872889237 := by
  unfold tailWord_1032172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823202808312299894133385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25097603744416399858844513 18823202808312299894133385)
  ·
    refine ⟨14117402106234224920600039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18823202808312299894133385 14117402106234224920600039)
    ·
      refine ⟨21176103159351337380900059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14117402106234224920600039 21176103159351337380900059)
      ·
        refine ⟨31764154739027006071350089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176103159351337380900059 31764154739027006071350089)
        ·
          refine ⟨23823116054270254553512567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31764154739027006071350089 23823116054270254553512567)
          ·
            refine ⟨35734674081405381830268851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23823116054270254553512567 35734674081405381830268851)
            ·
              refine ⟨53602011122108072745403277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35734674081405381830268851 53602011122108072745403277)
              ·
                refine ⟨20100754170790527279526229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53602011122108072745403277 20100754170790527279526229)
                ·
                  refine ⟨58888928234737872889237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20100754170790527279526229 58888928234737872889237)
                  ·
                    rfl

theorem cell23_1032172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_1032172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032172 prefixEnd_1032172 := by exact prefixLift 1032172
  have htrace : WordTrace (prefixWord ++ tailWord_1032172) baseStart_1032172 baseEnd_1032172 := by
    simpa [prefixWord, tailWord_1032172, baseEnd_1032172] using wordTrace_append hprefix tailTrace_1032172
  have hstable : (prefixWord ++ tailWord_1032172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032172).length < 2 ^ (prefixWord ++ tailWord_1032172).sum := by decide
  have hdescent : baseEnd_1032172 < baseStart_1032172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032189 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 6]
def baseStart_1032189 : Nat := 118140960795 + 1032189 * 2 ^ 59
def prefixEnd_1032189 : Nat := 4983230072969 + 3 ^ 40 * 1032189 * 2
def baseEnd_1032189 : Nat := 58889898142640809943395

theorem tailTrace_1032189 : CollatzResearch.WordTrace tailWord_1032189 prefixEnd_1032189 58889898142640809943395 := by
  unfold tailWord_1032189
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647025657563011691635621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25098017105042007794423747 37647025657563011691635621)
  ·
    refine ⟨7058817310793064692181679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37647025657563011691635621 7058817310793064692181679)
    ·
      refine ⟨10588225966189597038272519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058817310793064692181679 10588225966189597038272519)
      ·
        refine ⟨15882338949284395557408779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588225966189597038272519 15882338949284395557408779)
        ·
          refine ⟨23823508423926593336113169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15882338949284395557408779 23823508423926593336113169)
          ·
            refine ⟨17867631317944945002084877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23823508423926593336113169 17867631317944945002084877)
            ·
              refine ⟨6700361744229354375781829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17867631317944945002084877 6700361744229354375781829)
              ·
                refine ⟨1256317827043003945459093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6700361744229354375781829 1256317827043003945459093)
                ·
                  refine ⟨58889898142640809943395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1256317827043003945459093 58889898142640809943395)
                  ·
                    rfl

theorem cell23_1032189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_1032189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032189 prefixEnd_1032189 := by exact prefixLift 1032189
  have htrace : WordTrace (prefixWord ++ tailWord_1032189) baseStart_1032189 baseEnd_1032189 := by
    simpa [prefixWord, tailWord_1032189, baseEnd_1032189] using wordTrace_append hprefix tailTrace_1032189
  have hstable : (prefixWord ++ tailWord_1032189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032189).length < 2 ^ (prefixWord ++ tailWord_1032189).sum := by decide
  have hdescent : baseEnd_1032189 < baseStart_1032189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032193 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1032193 : Nat := 118140960795 + 1032193 * 2 ^ 59
def prefixEnd_1032193 : Nat := 4983230072969 + 3 ^ 40 * 1032193 * 2
def baseEnd_1032193 : Nat := 176670379068795091280179

theorem tailTrace_1032193 : CollatzResearch.WordTrace tailWord_1032193 prefixEnd_1032193 176670379068795091280179 := by
  unfold tailWord_1032193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647171549548520374781233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25098114366365680249854155 37647171549548520374781233)
  ·
    refine ⟨28235378662161390281085925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37647171549548520374781233 28235378662161390281085925)
    ·
      refine ⟨5294133499155260677703611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28235378662161390281085925 5294133499155260677703611)
      ·
        refine ⟨7941200248732891016555417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294133499155260677703611 7941200248732891016555417)
        ·
          refine ⟨5955900186549668262416563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7941200248732891016555417 5955900186549668262416563)
          ·
            refine ⟨8933850279824502393624845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5955900186549668262416563 8933850279824502393624845)
            ·
              refine ⟨3350193854934188397609317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8933850279824502393624845 3350193854934188397609317)
              ·
                refine ⟨628161347800160324551747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3350193854934188397609317 628161347800160324551747)
                ·
                  refine ⟨942242021700240486827621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628161347800160324551747 942242021700240486827621)
                  ·
                    refine ⟨176670379068795091280179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942242021700240486827621 176670379068795091280179)
                    ·
                      rfl

theorem cell23_1032193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1032193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032193 prefixEnd_1032193 := by exact prefixLift 1032193
  have htrace : WordTrace (prefixWord ++ tailWord_1032193) baseStart_1032193 baseEnd_1032193 := by
    simpa [prefixWord, tailWord_1032193, baseEnd_1032193] using wordTrace_append hprefix tailTrace_1032193
  have hstable : (prefixWord ++ tailWord_1032193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032193).length < 2 ^ (prefixWord ++ tailWord_1032193).sum := by decide
  have hdescent : baseEnd_1032193 < baseStart_1032193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032239 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_1032239 : Nat := 118140960795 + 1032239 * 2 ^ 59
def prefixEnd_1032239 : Nat := 4983230072969 + 3 ^ 40 * 1032239 * 2
def baseEnd_1032239 : Nat := 530034757316492093865325

theorem tailTrace_1032239 : CollatzResearch.WordTrace tailWord_1032239 prefixEnd_1032239 530034757316492093865325 := by
  unfold tailWord_1032239
  simp only [CollatzResearch.WordTrace]
  refine ⟨37648849307381870230955771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25099232871587913487303847 37648849307381870230955771)
  ·
    refine ⟨56473273961072805346433657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37648849307381870230955771 56473273961072805346433657)
    ·
      refine ⟨42354955470804604009825243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56473273961072805346433657 42354955470804604009825243)
      ·
        refine ⟨63532433206206906014737865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42354955470804604009825243 63532433206206906014737865)
        ·
          refine ⟨47649324904655179511053399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63532433206206906014737865 47649324904655179511053399)
          ·
            refine ⟨71473987356982769266580099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47649324904655179511053399 71473987356982769266580099)
            ·
              refine ⟨107210981035474153899870149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71473987356982769266580099 107210981035474153899870149)
              ·
                refine ⟨20102058944151403856225653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107210981035474153899870149 20102058944151403856225653)
                ·
                  refine ⟨1884568026014194111521155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20102058944151403856225653 1884568026014194111521155)
                  ·
                    refine ⟨2826852039021291167281733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1884568026014194111521155 2826852039021291167281733)
                    ·
                      refine ⟨530034757316492093865325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2826852039021291167281733 530034757316492093865325)
                      ·
                        rfl

theorem cell23_1032239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_1032239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032239 prefixEnd_1032239 := by exact prefixLift 1032239
  have htrace : WordTrace (prefixWord ++ tailWord_1032239) baseStart_1032239 baseEnd_1032239 := by
    simpa [prefixWord, tailWord_1032239, baseEnd_1032239] using wordTrace_append hprefix tailTrace_1032239
  have hstable : (prefixWord ++ tailWord_1032239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032239).length < 2 ^ (prefixWord ++ tailWord_1032239).sum := by decide
  have hdescent : baseEnd_1032239 < baseStart_1032239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032259 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3]
def baseStart_1032259 : Nat := 118140960795 + 1032259 * 2 ^ 59
def prefixEnd_1032259 : Nat := 4983230072969 + 3 ^ 40 * 1032259 * 2
def baseEnd_1032259 : Nat := 530045026929582015615233

theorem tailTrace_1032259 : CollatzResearch.WordTrace tailWord_1032259 prefixEnd_1032259 530045026929582015615233 := by
  unfold tailWord_1032259
  simp only [CollatzResearch.WordTrace]
  refine ⟨37649578767309413646683831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25099719178206275764455887 37649578767309413646683831)
  ·
    refine ⟨56474368150964120470025747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37649578767309413646683831 56474368150964120470025747)
    ·
      refine ⟨84711552226446180705038621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56474368150964120470025747 84711552226446180705038621)
      ·
        refine ⟨31766832084917317764389483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84711552226446180705038621 31766832084917317764389483)
        ·
          refine ⟨47650248127375976646584225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31766832084917317764389483 47650248127375976646584225)
          ·
            refine ⟨35737686095531982484938169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47650248127375976646584225 35737686095531982484938169)
            ·
              refine ⟨26803264571648986863703627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35737686095531982484938169 26803264571648986863703627)
              ·
                refine ⟨40204896857473480295555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803264571648986863703627 40204896857473480295555441)
                ·
                  refine ⟨30153672643105110221666581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40204896857473480295555441 30153672643105110221666581)
                  ·
                    refine ⟨1413453405145552041640621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30153672643105110221666581 1413453405145552041640621)
                    ·
                      refine ⟨530045026929582015615233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1413453405145552041640621 530045026929582015615233)
                      ·
                        rfl

theorem cell23_1032259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_1032259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032259 prefixEnd_1032259 := by exact prefixLift 1032259
  have htrace : WordTrace (prefixWord ++ tailWord_1032259) baseStart_1032259 baseEnd_1032259 := by
    simpa [prefixWord, tailWord_1032259, baseEnd_1032259] using wordTrace_append hprefix tailTrace_1032259
  have hstable : (prefixWord ++ tailWord_1032259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032259).length < 2 ^ (prefixWord ++ tailWord_1032259).sum := by decide
  have hdescent : baseEnd_1032259 < baseStart_1032259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032293 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1032293 : Nat := 118140960795 + 1032293 * 2 ^ 59
def prefixEnd_1032293 : Nat := 4983230072969 + 3 ^ 40 * 1032293 * 2
def baseEnd_1032293 : Nat := 530062485271834882590077

theorem tailTrace_1032293 : CollatzResearch.WordTrace tailWord_1032293 prefixEnd_1032293 530062485271834882590077 := by
  unfold tailWord_1032293
  simp only [CollatzResearch.WordTrace]
  refine ⟨37650818849186237453421533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25100545899457491635614355 37650818849186237453421533)
  ·
    refine ⟨14119057068444839045033075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37650818849186237453421533 14119057068444839045033075)
    ·
      refine ⟨21178585602667258567549613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14119057068444839045033075 21178585602667258567549613)
      ·
        refine ⟨7941969601000221962831105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21178585602667258567549613 7941969601000221962831105)
        ·
          refine ⟨5956477200750166472123329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7941969601000221962831105 5956477200750166472123329)
          ·
            refine ⟨4467357900562624854092497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956477200750166472123329 4467357900562624854092497)
            ·
              refine ⟨3350518425421968640569373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467357900562624854092497 3350518425421968640569373)
              ·
                refine ⟨1256444409533238240213515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350518425421968640569373 1256444409533238240213515)
                ·
                  refine ⟨1884666614299857360320273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256444409533238240213515 1884666614299857360320273)
                  ·
                    refine ⟨1413499960724893020240205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1884666614299857360320273 1413499960724893020240205)
                    ·
                      refine ⟨530062485271834882590077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1413499960724893020240205 530062485271834882590077)
                      ·
                        rfl

theorem cell23_1032293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1032293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032293 prefixEnd_1032293 := by exact prefixLift 1032293
  have htrace : WordTrace (prefixWord ++ tailWord_1032293) baseStart_1032293 baseEnd_1032293 := by
    simpa [prefixWord, tailWord_1032293, baseEnd_1032293] using wordTrace_append hprefix tailTrace_1032293
  have hstable : (prefixWord ++ tailWord_1032293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032293).length < 2 ^ (prefixWord ++ tailWord_1032293).sum := by decide
  have hdescent : baseEnd_1032293 < baseStart_1032293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032339 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 6]
def baseStart_1032339 : Nat := 118140960795 + 1032339 * 2 ^ 59
def prefixEnd_1032339 : Nat := 4983230072969 + 3 ^ 40 * 1032339 * 2
def baseEnd_1032339 : Nat := 176695368460647234204955

theorem tailTrace_1032339 : CollatzResearch.WordTrace tailWord_1032339 prefixEnd_1032339 176695368460647234204955 := by
  unfold tailWord_1032339
  simp only [CollatzResearch.WordTrace]
  refine ⟨37652496607019587309596071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25101664404679724873064047 37652496607019587309596071)
  ·
    refine ⟨56478744910529380964394107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37652496607019587309596071 56478744910529380964394107)
    ·
      refine ⟨84718117365794071446591161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56478744910529380964394107 84718117365794071446591161)
      ·
        refine ⟨63538588024345553584943371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84718117365794071446591161 63538588024345553584943371)
        ·
          refine ⟨95307882036518330377415057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63538588024345553584943371 95307882036518330377415057)
          ·
            refine ⟨71480911527388747783061293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95307882036518330377415057 71480911527388747783061293)
            ·
              refine ⟨26805341822770780418647985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71480911527388747783061293 26805341822770780418647985)
              ·
                refine ⟨20104006367078085313985989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26805341822770780418647985 20104006367078085313985989)
                ·
                  refine ⟨3769501193827140996372373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20104006367078085313985989 3769501193827140996372373)
                  ·
                    refine ⟨176695368460647234204955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3769501193827140996372373 176695368460647234204955)
                    ·
                      rfl

theorem cell23_1032339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_1032339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032339 prefixEnd_1032339 := by exact prefixLift 1032339
  have htrace : WordTrace (prefixWord ++ tailWord_1032339) baseStart_1032339 baseEnd_1032339 := by
    simpa [prefixWord, tailWord_1032339, baseEnd_1032339] using wordTrace_append hprefix tailTrace_1032339
  have hstable : (prefixWord ++ tailWord_1032339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032339).length < 2 ^ (prefixWord ++ tailWord_1032339).sum := by decide
  have hdescent : baseEnd_1032339 < baseStart_1032339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 10, 2, 2]
def baseStart_1032363 : Nat := 118140960795 + 1032363 * 2 ^ 59
def prefixEnd_1032363 : Nat := 4983230072969 + 3 ^ 40 * 1032363 * 2
def baseEnd_1032363 : Nat := 530098428917649608714755

theorem tailTrace_1032363 : CollatzResearch.WordTrace tailWord_1032363 prefixEnd_1032363 530098428917649608714755 := by
  unfold tailWord_1032363
  simp only [CollatzResearch.WordTrace]
  refine ⟨37653371958932639408469743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25102247972621759605646495 37653371958932639408469743)
  ·
    refine ⟨56480057938398959112704615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37653371958932639408469743 56480057938398959112704615)
    ·
      refine ⟨84720086907598438669056923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56480057938398959112704615 84720086907598438669056923)
      ·
        refine ⟨127080130361397658003585385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84720086907598438669056923 127080130361397658003585385)
        ·
          refine ⟨95310097771048243502689039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127080130361397658003585385 95310097771048243502689039)
          ·
            refine ⟨142965146656572365254033559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95310097771048243502689039 142965146656572365254033559)
            ·
              refine ⟨214447719984858547881050339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142965146656572365254033559 214447719984858547881050339)
              ·
                refine ⟨321671579977287821821575509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214447719984858547881050339 321671579977287821821575509)
                ·
                  refine ⟨942397206964710415492897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 321671579977287821821575509 942397206964710415492897)
                  ·
                    refine ⟨706797905223532811619673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 942397206964710415492897 706797905223532811619673)
                    ·
                      refine ⟨530098428917649608714755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706797905223532811619673 530098428917649608714755)
                      ·
                        rfl

theorem cell23_1032363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2, 2].length) (baseStart_1032363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032363 prefixEnd_1032363 := by exact prefixLift 1032363
  have htrace : WordTrace (prefixWord ++ tailWord_1032363) baseStart_1032363 baseEnd_1032363 := by
    simpa [prefixWord, tailWord_1032363, baseEnd_1032363] using wordTrace_append hprefix tailTrace_1032363
  have hstable : (prefixWord ++ tailWord_1032363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032363).length < 2 ^ (prefixWord ++ tailWord_1032363).sum := by decide
  have hdescent : baseEnd_1032363 < baseStart_1032363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032376 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1032376 : Nat := 118140960795 + 1032376 * 2 ^ 59
def prefixEnd_1032376 : Nat := 4983230072969 + 3 ^ 40 * 1032376 * 2
def baseEnd_1032376 : Nat := 530105104166158057852195

theorem tailTrace_1032376 : CollatzResearch.WordTrace tailWord_1032376 prefixEnd_1032376 530105104166158057852195 := by
  unfold tailWord_1032376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18826923053942771314346491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25102564071923695085795321 18826923053942771314346491)
  ·
    refine ⟨28240384580914156971519737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18826923053942771314346491 28240384580914156971519737)
    ·
      refine ⟨21180288435685617728639803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28240384580914156971519737 21180288435685617728639803)
      ·
        refine ⟨31770432653528426592959705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180288435685617728639803 31770432653528426592959705)
        ·
          refine ⟨23827824490146319944719779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770432653528426592959705 23827824490146319944719779)
          ·
            refine ⟨35741736735219479917079669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23827824490146319944719779 35741736735219479917079669)
            ·
              refine ⟨3350787818926826242226219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35741736735219479917079669 3350787818926826242226219)
              ·
                refine ⟨5026181728390239363339329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350787818926826242226219 5026181728390239363339329)
                ·
                  refine ⟨3769636296292679522504497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026181728390239363339329 3769636296292679522504497)
                  ·
                    refine ⟨2827227222219509641878373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3769636296292679522504497 2827227222219509641878373)
                    ·
                      refine ⟨530105104166158057852195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2827227222219509641878373 530105104166158057852195)
                      ·
                        rfl

theorem cell23_1032376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1032376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032376 prefixEnd_1032376 := by exact prefixLift 1032376
  have htrace : WordTrace (prefixWord ++ tailWord_1032376) baseStart_1032376 baseEnd_1032376 := by
    simpa [prefixWord, tailWord_1032376, baseEnd_1032376] using wordTrace_append hprefix tailTrace_1032376
  have hstable : (prefixWord ++ tailWord_1032376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032376).length < 2 ^ (prefixWord ++ tailWord_1032376).sum := by decide
  have hdescent : baseEnd_1032376 < baseStart_1032376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032416 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_1032416 : Nat := 118140960795 + 1032416 * 2 ^ 59
def prefixEnd_1032416 : Nat := 4983230072969 + 3 ^ 40 * 1032416 * 2
def baseEnd_1032416 : Nat := 176708547797445967117337

theorem tailTrace_1032416 : CollatzResearch.WordTrace tailWord_1032416 prefixEnd_1032416 176708547797445967117337 := by
  unfold tailWord_1032416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827652513870314730074551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25103536685160419640099401 18827652513870314730074551)
  ·
    refine ⟨28241478770805472095111827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18827652513870314730074551 28241478770805472095111827)
    ·
      refine ⟨42362218156208208142667741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28241478770805472095111827 42362218156208208142667741)
      ·
        refine ⟨15885831808578078053500403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42362218156208208142667741 15885831808578078053500403)
        ·
          refine ⟨23828747712867117080250605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885831808578078053500403 23828747712867117080250605)
          ·
            refine ⟨8935780392325168905093977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23828747712867117080250605 8935780392325168905093977)
            ·
              refine ⟨6701835294243876678820483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935780392325168905093977 6701835294243876678820483)
              ·
                refine ⟨10052752941365815018230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701835294243876678820483 10052752941365815018230725)
                ·
                  refine ⟨1884891176506090315918261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10052752941365815018230725 1884891176506090315918261)
                  ·
                    refine ⟨176708547797445967117337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1884891176506090315918261 176708547797445967117337)
                    ·
                      rfl

theorem cell23_1032416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_1032416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032416 prefixEnd_1032416 := by exact prefixLift 1032416
  have htrace : WordTrace (prefixWord ++ tailWord_1032416) baseStart_1032416 baseEnd_1032416 := by
    simpa [prefixWord, tailWord_1032416, baseEnd_1032416] using wordTrace_append hprefix tailTrace_1032416
  have hstable : (prefixWord ++ tailWord_1032416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032416).length < 2 ^ (prefixWord ++ tailWord_1032416).sum := by decide
  have hdescent : baseEnd_1032416 < baseStart_1032416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032426 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1032426 : Nat := 118140960795 + 1032426 * 2 ^ 59
def prefixEnd_1032426 : Nat := 4983230072969 + 3 ^ 40 * 1032426 * 2
def baseEnd_1032426 : Nat := 530130778198882862226965

theorem tailTrace_1032426 : CollatzResearch.WordTrace tailWord_1032426 prefixEnd_1032426 530130778198882862226965 := by
  unfold tailWord_1032426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413917439426100292003283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25103779838469600778675421 9413917439426100292003283)
  ·
    refine ⟨14120876159139150438004925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413917439426100292003283 14120876159139150438004925)
    ·
      refine ⟨5295328559677181414251847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14120876159139150438004925 5295328559677181414251847)
      ·
        refine ⟨7942992839515772121377771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295328559677181414251847 7942992839515772121377771)
        ·
          refine ⟨11914489259273658182066657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942992839515772121377771 11914489259273658182066657)
          ·
            refine ⟨8935866944455243636549993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11914489259273658182066657 8935866944455243636549993)
            ·
              refine ⟨6701900208341432727412495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935866944455243636549993 6701900208341432727412495)
              ·
                refine ⟨10052850312512149091118743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701900208341432727412495 10052850312512149091118743)
                ·
                  refine ⟨15079275468768223636678115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052850312512149091118743 15079275468768223636678115)
                  ·
                    refine ⟨22618913203152335455017173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15079275468768223636678115 22618913203152335455017173)
                    ·
                      refine ⟨530130778198882862226965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22618913203152335455017173 530130778198882862226965)
                      ·
                        rfl

theorem cell23_1032426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1032426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032426 prefixEnd_1032426 := by exact prefixLift 1032426
  have htrace : WordTrace (prefixWord ++ tailWord_1032426) baseStart_1032426 baseEnd_1032426 := by
    simpa [prefixWord, tailWord_1032426, baseEnd_1032426] using wordTrace_append hprefix tailTrace_1032426
  have hstable : (prefixWord ++ tailWord_1032426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032426).length < 2 ^ (prefixWord ++ tailWord_1032426).sum := by decide
  have hdescent : baseEnd_1032426 < baseStart_1032426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_1032453 : Nat := 118140960795 + 1032453 * 2 ^ 59
def prefixEnd_1032453 : Nat := 4983230072969 + 3 ^ 40 * 1032453 * 2
def baseEnd_1032453 : Nat := 530144642176554256589341

theorem tailTrace_1032453 : CollatzResearch.WordTrace tailWord_1032453 prefixEnd_1032453 530144642176554256589341 := by
  unfold tailWord_1032453
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656654528606584779246013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25104436352404389852830675 37656654528606584779246013)
  ·
    refine ⟨14121245448227469292217255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37656654528606584779246013 14121245448227469292217255)
    ·
      refine ⟨21181868172341203938325883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14121245448227469292217255 21181868172341203938325883)
      ·
        refine ⟨31772802258511805907488825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21181868172341203938325883 31772802258511805907488825)
        ·
          refine ⟨23829601693883854430616619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31772802258511805907488825 23829601693883854430616619)
          ·
            refine ⟨35744402540825781645924929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23829601693883854430616619 35744402540825781645924929)
            ·
              refine ⟨26808301905619336234443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35744402540825781645924929 26808301905619336234443697)
              ·
                refine ⟨20106226429214502175832773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26808301905619336234443697 20106226429214502175832773)
                ·
                  refine ⟨3769917455477719157968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20106226429214502175832773 3769917455477719157968645)
                  ·
                    refine ⟨706859522902072342119121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3769917455477719157968645 706859522902072342119121)
                    ·
                      refine ⟨530144642176554256589341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 706859522902072342119121 530144642176554256589341)
                      ·
                        rfl

theorem cell23_1032453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_1032453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032453 prefixEnd_1032453 := by exact prefixLift 1032453
  have htrace : WordTrace (prefixWord ++ tailWord_1032453) baseStart_1032453 baseEnd_1032453 := by
    simpa [prefixWord, tailWord_1032453, baseEnd_1032453] using wordTrace_append hprefix tailTrace_1032453
  have hstable : (prefixWord ++ tailWord_1032453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032453).length < 2 ^ (prefixWord ++ tailWord_1032453).sum := by decide
  have hdescent : baseEnd_1032453 < baseStart_1032453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032480 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_1032480 : Nat := 118140960795 + 1032480 * 2 ^ 59
def prefixEnd_1032480 : Nat := 4983230072969 + 3 ^ 40 * 1032480 * 2
def baseEnd_1032480 : Nat := 176719502051408550317239

theorem tailTrace_1032480 : CollatzResearch.WordTrace tailWord_1032480 prefixEnd_1032480 176719502051408550317239 := by
  unfold tailWord_1032480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18828819649754384195239447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25105092866339178926985929 18828819649754384195239447)
  ·
    refine ⟨28243229474631576292859171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18828819649754384195239447 28243229474631576292859171)
    ·
      refine ⟨42364844211947364439288757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28243229474631576292859171 42364844211947364439288757)
      ·
        refine ⟨3971704144870065416183321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42364844211947364439288757 3971704144870065416183321)
        ·
          refine ⟨2978778108652549062137491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3971704144870065416183321 2978778108652549062137491)
          ·
            refine ⟨4468167162978823593206237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978778108652549062137491 4468167162978823593206237)
            ·
              refine ⟨1675562686117058847452339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4468167162978823593206237 1675562686117058847452339)
              ·
                refine ⟨2513344029175588271178509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675562686117058847452339 2513344029175588271178509)
                ·
                  refine ⟨942504010940845601691941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2513344029175588271178509 942504010940845601691941)
                  ·
                    refine ⟨176719502051408550317239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942504010940845601691941 176719502051408550317239)
                    ·
                      rfl

theorem cell23_1032480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_1032480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032480 prefixEnd_1032480 := by exact prefixLift 1032480
  have htrace : WordTrace (prefixWord ++ tailWord_1032480) baseStart_1032480 baseEnd_1032480 := by
    simpa [prefixWord, tailWord_1032480, baseEnd_1032480] using wordTrace_append hprefix tailTrace_1032480
  have hstable : (prefixWord ++ tailWord_1032480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032480).length < 2 ^ (prefixWord ++ tailWord_1032480).sum := by decide
  have hdescent : baseEnd_1032480 < baseStart_1032480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032543 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1032543 : Nat := 118140960795 + 1032543 * 2 ^ 59
def prefixEnd_1032543 : Nat := 4983230072969 + 3 ^ 40 * 1032543 * 2
def baseEnd_1032543 : Nat := 530190855435458904463927

theorem tailTrace_1032543 : CollatzResearch.WordTrace tailWord_1032543 prefixEnd_1032543 530190855435458904463927 := by
  unfold tailWord_1032543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37659937098280530150022283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25106624732187020100014855 37659937098280530150022283)
  ·
    refine ⟨56489905647420795225033425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37659937098280530150022283 56489905647420795225033425)
    ·
      refine ⟨42367429235565596418775069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56489905647420795225033425 42367429235565596418775069)
      ·
        refine ⟨15887785963337098657040651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42367429235565596418775069 15887785963337098657040651)
        ·
          refine ⟨23831678945005647985560977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15887785963337098657040651 23831678945005647985560977)
          ·
            refine ⟨17873759208754235989170733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23831678945005647985560977 17873759208754235989170733)
            ·
              refine ⟨6702659703282838495939025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17873759208754235989170733 6702659703282838495939025)
              ·
                refine ⟨5026994777462128871954269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702659703282838495939025 5026994777462128871954269)
                ·
                  refine ⟨1885123041548298326982851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5026994777462128871954269 1885123041548298326982851)
                  ·
                    refine ⟨2827684562322447490474277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885123041548298326982851 2827684562322447490474277)
                    ·
                      refine ⟨530190855435458904463927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2827684562322447490474277 530190855435458904463927)
                      ·
                        rfl

theorem cell23_1032543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1032543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032543 prefixEnd_1032543 := by exact prefixLift 1032543
  have htrace : WordTrace (prefixWord ++ tailWord_1032543) baseStart_1032543 baseEnd_1032543 := by
    simpa [prefixWord, tailWord_1032543, baseEnd_1032543] using wordTrace_append hprefix tailTrace_1032543
  have hstable : (prefixWord ++ tailWord_1032543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032543).length < 2 ^ (prefixWord ++ tailWord_1032543).sum := by decide
  have hdescent : baseEnd_1032543 < baseStart_1032543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032553 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_1032553 : Nat := 118140960795 + 1032553 * 2 ^ 59
def prefixEnd_1032553 : Nat := 4983230072969 + 3 ^ 40 * 1032553 * 2
def baseEnd_1032553 : Nat := 176731996747334621779627

theorem tailTrace_1032553 : CollatzResearch.WordTrace tailWord_1032553 prefixEnd_1032553 176731996747334621779627 := by
  unfold tailWord_1032553
  simp only [CollatzResearch.WordTrace]
  refine ⟨37660301828244301857886313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25106867885496201238590875 37660301828244301857886313)
  ·
    refine ⟨28245226371183226393414735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37660301828244301857886313 28245226371183226393414735)
    ·
      refine ⟨42367839556774839590122103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28245226371183226393414735 42367839556774839590122103)
      ·
        refine ⟨63551759335162259385183155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42367839556774839590122103 63551759335162259385183155)
        ·
          refine ⟨95327639002743389077774733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63551759335162259385183155 95327639002743389077774733)
          ·
            refine ⟨35747864626028770904165525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95327639002743389077774733 35747864626028770904165525)
            ·
              refine ⟨1675681154345098636132759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35747864626028770904165525 1675681154345098636132759)
              ·
                refine ⟨2513521731517647954199139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675681154345098636132759 2513521731517647954199139)
                ·
                  refine ⟨3770282597276471931298709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513521731517647954199139 3770282597276471931298709)
                  ·
                    refine ⟨176731996747334621779627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3770282597276471931298709 176731996747334621779627)
                    ·
                      rfl

theorem cell23_1032553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_1032553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032553 prefixEnd_1032553 := by exact prefixLift 1032553
  have htrace : WordTrace (prefixWord ++ tailWord_1032553) baseStart_1032553 baseEnd_1032553 := by
    simpa [prefixWord, tailWord_1032553, baseEnd_1032553] using wordTrace_append hprefix tailTrace_1032553
  have hstable : (prefixWord ++ tailWord_1032553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032553).length < 2 ^ (prefixWord ++ tailWord_1032553).sum := by decide
  have hdescent : baseEnd_1032553 < baseStart_1032553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032577 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1032577 : Nat := 118140960795 + 1032577 * 2 ^ 59
def prefixEnd_1032577 : Nat := 4983230072969 + 3 ^ 40 * 1032577 * 2
def baseEnd_1032577 : Nat := 530208313777711771438771

theorem tailTrace_1032577 : CollatzResearch.WordTrace tailWord_1032577 prefixEnd_1032577 530208313777711771438771 := by
  unfold tailWord_1032577
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661177180157353956759985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25107451453438235971173323 37661177180157353956759985)
  ·
    refine ⟨28245882885118015467569989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37661177180157353956759985 28245882885118015467569989)
    ·
      refine ⟨5296103040959627900169373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28245882885118015467569989 5296103040959627900169373)
      ·
        refine ⟨1986038640359860462563515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5296103040959627900169373 1986038640359860462563515)
        ·
          refine ⟨2979057960539790693845273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986038640359860462563515 2979057960539790693845273)
          ·
            refine ⟨2234293470404843020383955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979057960539790693845273 2234293470404843020383955)
            ·
              refine ⟨3351440205607264530575933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234293470404843020383955 3351440205607264530575933)
              ·
                refine ⟨1256790077102724198965975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351440205607264530575933 1256790077102724198965975)
                ·
                  refine ⟨1885185115654086298448963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256790077102724198965975 1885185115654086298448963)
                  ·
                    refine ⟨2827777673481129447673445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885185115654086298448963 2827777673481129447673445)
                    ·
                      refine ⟨530208313777711771438771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2827777673481129447673445 530208313777711771438771)
                      ·
                        rfl

theorem cell23_1032577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1032577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032577 prefixEnd_1032577 := by exact prefixLift 1032577
  have htrace : WordTrace (prefixWord ++ tailWord_1032577) baseStart_1032577 baseEnd_1032577 := by
    simpa [prefixWord, tailWord_1032577, baseEnd_1032577] using wordTrace_append hprefix tailTrace_1032577
  have hstable : (prefixWord ++ tailWord_1032577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032577).length < 2 ^ (prefixWord ++ tailWord_1032577).sum := by decide
  have hdescent : baseEnd_1032577 < baseStart_1032577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032587 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 2, 4]
def baseStart_1032587 : Nat := 118140960795 + 1032587 * 2 ^ 59
def prefixEnd_1032587 : Nat := 4983230072969 + 3 ^ 40 * 1032587 * 2
def baseEnd_1032587 : Nat := 176737816194752244104575

theorem tailTrace_1032587 : CollatzResearch.WordTrace tailWord_1032587 prefixEnd_1032587 176737816194752244104575 := by
  unfold tailWord_1032587
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661541910121125664624015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25107694606747417109749343 37661541910121125664624015)
  ·
    refine ⟨56492312865181688496936023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37661541910121125664624015 56492312865181688496936023)
    ·
      refine ⟨84738469297772532745404035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56492312865181688496936023 84738469297772532745404035)
      ·
        refine ⟨127107703946658799118106053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84738469297772532745404035 127107703946658799118106053)
        ·
          refine ⟨23832694489998524834644885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127107703946658799118106053 23832694489998524834644885)
          ·
            refine ⟨1117157554218680851623979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23832694489998524834644885 1117157554218680851623979)
            ·
              refine ⟨1675736331328021277435969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117157554218680851623979 1675736331328021277435969)
              ·
                refine ⟨1256802248496015958076977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675736331328021277435969 1256802248496015958076977)
                ·
                  refine ⟨942601686372011968557733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1256802248496015958076977 942601686372011968557733)
                  ·
                    refine ⟨176737816194752244104575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942601686372011968557733 176737816194752244104575)
                    ·
                      rfl

theorem cell23_1032587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 4].length) (baseStart_1032587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032587 prefixEnd_1032587 := by exact prefixLift 1032587
  have htrace : WordTrace (prefixWord ++ tailWord_1032587) baseStart_1032587 baseEnd_1032587 := by
    simpa [prefixWord, tailWord_1032587, baseEnd_1032587] using wordTrace_append hprefix tailTrace_1032587
  have hstable : (prefixWord ++ tailWord_1032587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032587).length < 2 ^ (prefixWord ++ tailWord_1032587).sum := by decide
  have hdescent : baseEnd_1032587 < baseStart_1032587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032661 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1032661 : Nat := 118140960795 + 1032661 * 2 ^ 59
def prefixEnd_1032661 : Nat := 4983230072969 + 3 ^ 40 * 1032661 * 2
def baseEnd_1032661 : Nat := 530251446152689442788385

theorem tailTrace_1032661 : CollatzResearch.WordTrace tailWord_1032661 prefixEnd_1032661 530251446152689442788385 := by
  unfold tailWord_1032661
  simp only [CollatzResearch.WordTrace]
  refine ⟨37664240911853036302817837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25109493941235357535211891 37664240911853036302817837)
  ·
    refine ⟨14124090341944888613556689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37664240911853036302817837 14124090341944888613556689)
    ·
      refine ⟨10593067756458666460167517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14124090341944888613556689 10593067756458666460167517)
      ·
        refine ⟨3972400408671999922562819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10593067756458666460167517 3972400408671999922562819)
        ·
          refine ⟨5958600613007999883844229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972400408671999922562819 5958600613007999883844229)
          ·
            refine ⟨1117237614938999978220793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5958600613007999883844229 1117237614938999978220793)
            ·
              refine ⟨837928211204249983665595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117237614938999978220793 837928211204249983665595)
              ·
                refine ⟨1256892316806374975498393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837928211204249983665595 1256892316806374975498393)
                ·
                  refine ⟨942669237604781231623795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1256892316806374975498393 942669237604781231623795)
                  ·
                    refine ⟨1414003856407171847435693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 942669237604781231623795 1414003856407171847435693)
                    ·
                      refine ⟨530251446152689442788385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414003856407171847435693 530251446152689442788385)
                      ·
                        rfl

theorem cell23_1032661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1032661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032661 prefixEnd_1032661 := by exact prefixLift 1032661
  have htrace : WordTrace (prefixWord ++ tailWord_1032661) baseStart_1032661 baseEnd_1032661 := by
    simpa [prefixWord, tailWord_1032661, baseEnd_1032661] using wordTrace_append hprefix tailTrace_1032661
  have hstable : (prefixWord ++ tailWord_1032661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032661).length < 2 ^ (prefixWord ++ tailWord_1032661).sum := by decide
  have hdescent : baseEnd_1032661 < baseStart_1032661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032673 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 9]
def baseStart_1032673 : Nat := 118140960795 + 1032673 * 2 ^ 59
def prefixEnd_1032673 : Nat := 4983230072969 + 3 ^ 40 * 1032673 * 2
def baseEnd_1032673 : Nat := 58917511991171488426481

theorem tailTrace_1032673 : CollatzResearch.WordTrace tailWord_1032673 prefixEnd_1032673 58917511991171488426481 := by
  unfold tailWord_1032673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37664678587809562352254673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25109785725206374901503115 37664678587809562352254673)
  ·
    refine ⟨28248508940857171764191005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37664678587809562352254673 28248508940857171764191005)
    ·
      refine ⟨10593190852821439411571627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28248508940857171764191005 10593190852821439411571627)
      ·
        refine ⟨15889786279232159117357441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593190852821439411571627 15889786279232159117357441)
        ·
          refine ⟨11917339709424119338018081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15889786279232159117357441 11917339709424119338018081)
          ·
            refine ⟨8938004782068089503513561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11917339709424119338018081 8938004782068089503513561)
            ·
              refine ⟨6703503586551067127635171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938004782068089503513561 6703503586551067127635171)
              ·
                refine ⟨10055255379826600691452757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703503586551067127635171 10055255379826600691452757)
                ·
                  refine ⟨58917511991171488426481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10055255379826600691452757 58917511991171488426481)
                  ·
                    rfl

theorem cell23_1032673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_1032673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032673 prefixEnd_1032673 := by exact prefixLift 1032673
  have htrace : WordTrace (prefixWord ++ tailWord_1032673) baseStart_1032673 baseEnd_1032673 := by
    simpa [prefixWord, tailWord_1032673, baseEnd_1032673] using wordTrace_append hprefix tailTrace_1032673
  have hstable : (prefixWord ++ tailWord_1032673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032673).length < 2 ^ (prefixWord ++ tailWord_1032673).sum := by decide
  have hdescent : baseEnd_1032673 < baseStart_1032673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032700 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_1032700 : Nat := 118140960795 + 1032700 * 2 ^ 59
def prefixEnd_1032700 : Nat := 4983230072969 + 3 ^ 40 * 1032700 * 2
def baseEnd_1032700 : Nat := 530271471898214790200705

theorem tailTrace_1032700 : CollatzResearch.WordTrace tailWord_1032700 prefixEnd_1032700 530271471898214790200705 := by
  unfold tailWord_1032700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18832831679355872981743777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25110442239141163975658369 18832831679355872981743777)
  ·
    refine ⟨14124623759516904736307833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18832831679355872981743777 14124623759516904736307833)
    ·
      refine ⟨10593467819637678552230875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14124623759516904736307833 10593467819637678552230875)
      ·
        refine ⟨15890201729456517828346313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593467819637678552230875 15890201729456517828346313)
        ·
          refine ⟨11917651297092388371259735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15890201729456517828346313 11917651297092388371259735)
          ·
            refine ⟨17876476945638582556889603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917651297092388371259735 17876476945638582556889603)
            ·
              refine ⟨26814715418457873835334405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17876476945638582556889603 26814715418457873835334405)
              ·
                refine ⟨5027759140960851344125201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26814715418457873835334405 5027759140960851344125201)
                ·
                  refine ⟨3770819355720638508093901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027759140960851344125201 3770819355720638508093901)
                  ·
                    refine ⟨1414057258395239440535213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770819355720638508093901 1414057258395239440535213)
                    ·
                      refine ⟨530271471898214790200705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414057258395239440535213 530271471898214790200705)
                      ·
                        rfl

theorem cell23_1032700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_1032700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032700 prefixEnd_1032700 := by exact prefixLift 1032700
  have htrace : WordTrace (prefixWord ++ tailWord_1032700) baseStart_1032700 baseEnd_1032700 := by
    simpa [prefixWord, tailWord_1032700, baseEnd_1032700] using wordTrace_append hprefix tailTrace_1032700
  have hstable : (prefixWord ++ tailWord_1032700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032700).length < 2 ^ (prefixWord ++ tailWord_1032700).sum := by decide
  have hdescent : baseEnd_1032700 < baseStart_1032700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032713 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_1032713 : Nat := 118140960795 + 1032713 * 2 ^ 59
def prefixEnd_1032713 : Nat := 4983230072969 + 3 ^ 40 * 1032713 * 2
def baseEnd_1032713 : Nat := 530278147146723239338145

theorem tailTrace_1032713 : CollatzResearch.WordTrace tailWord_1032713 prefixEnd_1032713 530278147146723239338145 := by
  unfold tailWord_1032713
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666137507664649183710793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25110758338443099455807195 37666137507664649183710793)
  ·
    refine ⟨28249603130748486887783095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37666137507664649183710793 28249603130748486887783095)
    ·
      refine ⟨42374404696122730331674643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28249603130748486887783095 42374404696122730331674643)
      ·
        refine ⟨63561607044184095497511965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42374404696122730331674643 63561607044184095497511965)
        ·
          refine ⟨23835602641569035811566987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63561607044184095497511965 23835602641569035811566987)
          ·
            refine ⟨35753403962353553717350481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23835602641569035811566987 35753403962353553717350481)
            ·
              refine ⟨26815052971765165288012861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35753403962353553717350481 26815052971765165288012861)
              ·
                refine ⟨10055644864411936983004823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26815052971765165288012861 10055644864411936983004823)
                ·
                  refine ⟨15083467296617905474507235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055644864411936983004823 15083467296617905474507235)
                  ·
                    refine ⟨22625200944926858211760853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15083467296617905474507235 22625200944926858211760853)
                    ·
                      refine ⟨530278147146723239338145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22625200944926858211760853 530278147146723239338145)
                      ·
                        rfl

theorem cell23_1032713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_1032713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032713 prefixEnd_1032713 := by exact prefixLift 1032713
  have htrace : WordTrace (prefixWord ++ tailWord_1032713) baseStart_1032713 baseEnd_1032713 := by
    simpa [prefixWord, tailWord_1032713, baseEnd_1032713] using wordTrace_append hprefix tailTrace_1032713
  have hstable : (prefixWord ++ tailWord_1032713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032713).length < 2 ^ (prefixWord ++ tailWord_1032713).sum := by decide
  have hdescent : baseEnd_1032713 < baseStart_1032713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032757 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_1032757 : Nat := 118140960795 + 1032757 * 2 ^ 59
def prefixEnd_1032757 : Nat := 4983230072969 + 3 ^ 40 * 1032757 * 2
def baseEnd_1032757 : Nat := 530300740295521067187943

theorem tailTrace_1032757 : CollatzResearch.WordTrace tailWord_1032757 prefixEnd_1032757 530300740295521067187943 := by
  unfold tailWord_1032757
  simp only [CollatzResearch.WordTrace]
  refine ⟨37667742319505244698312525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25111828213003496465541683 37667742319505244698312525)
  ·
    refine ⟨14125403369814466761867197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37667742319505244698312525 14125403369814466761867197)
    ·
      refine ⟨5297026263680425035700199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14125403369814466761867197 5297026263680425035700199)
      ·
        refine ⟨7945539395520637553550299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297026263680425035700199 7945539395520637553550299)
        ·
          refine ⟨11918309093280956330325449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945539395520637553550299 11918309093280956330325449)
          ·
            refine ⟨8938731819960717247744087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918309093280956330325449 8938731819960717247744087)
            ·
              refine ⟨13408097729941075871616131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938731819960717247744087 13408097729941075871616131)
              ·
                refine ⟨20112146594911613807424197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408097729941075871616131 20112146594911613807424197)
                ·
                  refine ⟨3771027486545927588892037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20112146594911613807424197 3771027486545927588892037)
                  ·
                    refine ⟨707067653727361422917257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771027486545927588892037 707067653727361422917257)
                    ·
                      refine ⟨530300740295521067187943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707067653727361422917257 530300740295521067187943)
                      ·
                        rfl

theorem cell23_1032757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_1032757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032757 prefixEnd_1032757 := by exact prefixLift 1032757
  have htrace : WordTrace (prefixWord ++ tailWord_1032757) baseStart_1032757 baseEnd_1032757 := by
    simpa [prefixWord, tailWord_1032757, baseEnd_1032757] using wordTrace_append hprefix tailTrace_1032757
  have hstable : (prefixWord ++ tailWord_1032757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032757).length < 2 ^ (prefixWord ++ tailWord_1032757).sum := by decide
  have hdescent : baseEnd_1032757 < baseStart_1032757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032767 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 3, 4]
def baseStart_1032767 : Nat := 118140960795 + 1032767 * 2 ^ 59
def prefixEnd_1032767 : Nat := 4983230072969 + 3 ^ 40 * 1032767 * 2
def baseEnd_1032767 : Nat := 176768625034022009354299

theorem tailTrace_1032767 : CollatzResearch.WordTrace tailWord_1032767 prefixEnd_1032767 176768625034022009354299 := by
  unfold tailWord_1032767
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668107049469016406176555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25112071366312677604117703 37668107049469016406176555)
  ·
    refine ⟨56502160574203524609264833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37668107049469016406176555 56502160574203524609264833)
    ·
      refine ⟨42376620430652643456948625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56502160574203524609264833 42376620430652643456948625)
      ·
        refine ⟨31782465322989482592711469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42376620430652643456948625 31782465322989482592711469)
        ·
          refine ⟨11918424496121055972266801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31782465322989482592711469 11918424496121055972266801)
          ·
            refine ⟨8938818372090791979200101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918424496121055972266801 8938818372090791979200101)
            ·
              refine ⟨1676028444767023496100019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8938818372090791979200101 1676028444767023496100019)
              ·
                refine ⟨2514042667150535244150029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676028444767023496100019 2514042667150535244150029)
                ·
                  refine ⟨942766000181450716556261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2514042667150535244150029 942766000181450716556261)
                  ·
                    refine ⟨176768625034022009354299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942766000181450716556261 176768625034022009354299)
                    ·
                      rfl

theorem cell23_1032767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_1032767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032767 prefixEnd_1032767 := by exact prefixLift 1032767
  have htrace : WordTrace (prefixWord ++ tailWord_1032767) baseStart_1032767 baseEnd_1032767 := by
    simpa [prefixWord, tailWord_1032767, baseEnd_1032767] using wordTrace_append hprefix tailTrace_1032767
  have hstable : (prefixWord ++ tailWord_1032767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032767).length < 2 ^ (prefixWord ++ tailWord_1032767).sum := by decide
  have hdescent : baseEnd_1032767 < baseStart_1032767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032774 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1032774 : Nat := 118140960795 + 1032774 * 2 ^ 59
def prefixEnd_1032774 : Nat := 4983230072969 + 3 ^ 40 * 1032774 * 2
def baseEnd_1032774 : Nat := 530309469466647500675365

theorem tailTrace_1032774 : CollatzResearch.WordTrace tailWord_1032774 prefixEnd_1032774 530309469466647500675365 := by
  unfold tailWord_1032774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177136323763864268802543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25112241573629104401120917 1177136323763864268802543)
  ·
    refine ⟨1765704485645796403203815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177136323763864268802543 1765704485645796403203815)
    ·
      refine ⟨2648556728468694604805723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765704485645796403203815 2648556728468694604805723)
      ·
        refine ⟨3972835092703041907208585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648556728468694604805723 3972835092703041907208585)
        ·
          refine ⟨2979626319527281430406439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972835092703041907208585 2979626319527281430406439)
          ·
            refine ⟨4469439479290922145609659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979626319527281430406439 4469439479290922145609659)
            ·
              refine ⟨6704159218936383218414489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469439479290922145609659 6704159218936383218414489)
              ·
                refine ⟨5028119414202287413810867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6704159218936383218414489 5028119414202287413810867)
                ·
                  refine ⟨7542179121303431120716301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028119414202287413810867 7542179121303431120716301)
                  ·
                    refine ⟨2828317170488786670268613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7542179121303431120716301 2828317170488786670268613)
                    ·
                      refine ⟨530309469466647500675365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2828317170488786670268613 530309469466647500675365)
                      ·
                        rfl

theorem cell23_1032774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1032774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032774 prefixEnd_1032774 := by exact prefixLift 1032774
  have htrace : WordTrace (prefixWord ++ tailWord_1032774) baseStart_1032774 baseEnd_1032774 := by
    simpa [prefixWord, tailWord_1032774, baseEnd_1032774] using wordTrace_append hprefix tailTrace_1032774
  have hstable : (prefixWord ++ tailWord_1032774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032774).length < 2 ^ (prefixWord ++ tailWord_1032774).sum := by decide
  have hdescent : baseEnd_1032774 < baseStart_1032774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032801 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1032801 : Nat := 118140960795 + 1032801 * 2 ^ 59
def prefixEnd_1032801 : Nat := 4983230072969 + 3 ^ 40 * 1032801 * 2
def baseEnd_1032801 : Nat := 176774444481439631679247

theorem tailTrace_1032801 : CollatzResearch.WordTrace tailWord_1032801 prefixEnd_1032801 176774444481439631679247 := by
  unfold tailWord_1032801
  simp only [CollatzResearch.WordTrace]
  refine ⟨37669347131345840212914257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25112898087563893475276171 37669347131345840212914257)
  ·
    refine ⟨28252010348509380159685693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37669347131345840212914257 28252010348509380159685693)
    ·
      refine ⟨10594503880691017559882135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28252010348509380159685693 10594503880691017559882135)
      ·
        refine ⟨15891755821036526339823203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594503880691017559882135 15891755821036526339823203)
        ·
          refine ⟨23837633731554789509734805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15891755821036526339823203 23837633731554789509734805)
          ·
            refine ⟨1117389081166630758268819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23837633731554789509734805 1117389081166630758268819)
            ·
              refine ⟨1676083621749946137403229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117389081166630758268819 1676083621749946137403229)
              ·
                refine ⟨628531358156229801526211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676083621749946137403229 628531358156229801526211)
                ·
                  refine ⟨942797037234344702289317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628531358156229801526211 942797037234344702289317)
                  ·
                    refine ⟨176774444481439631679247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942797037234344702289317 176774444481439631679247)
                    ·
                      rfl

theorem cell23_1032801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1032801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032801 prefixEnd_1032801 := by exact prefixLift 1032801
  have htrace : WordTrace (prefixWord ++ tailWord_1032801) baseStart_1032801 baseEnd_1032801 := by
    simpa [prefixWord, tailWord_1032801, baseEnd_1032801] using wordTrace_append hprefix tailTrace_1032801
  have hstable : (prefixWord ++ tailWord_1032801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032801).length < 2 ^ (prefixWord ++ tailWord_1032801).sum := by decide
  have hdescent : baseEnd_1032801 < baseStart_1032801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032818 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1032818 : Nat := 118140960795 + 1032818 * 2 ^ 59
def prefixEnd_1032818 : Nat := 4983230072969 + 3 ^ 40 * 1032818 * 2
def baseEnd_1032818 : Nat := 176777354205148442841721

theorem tailTrace_1032818 : CollatzResearch.WordTrace tailWord_1032818 prefixEnd_1032818 176777354205148442841721 := by
  unfold tailWord_1032818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417491793071063029070777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25113311448189501410855405 9417491793071063029070777)
  ·
    refine ⟨7063118844803297271803083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9417491793071063029070777 7063118844803297271803083)
    ·
      refine ⟨10594678267204945907704625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063118844803297271803083 10594678267204945907704625)
      ·
        refine ⟨7946008700403709430778469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10594678267204945907704625 7946008700403709430778469)
        ·
          refine ⟨1489876631325695518270963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7946008700403709430778469 1489876631325695518270963)
          ·
            refine ⟨2234814946988543277406445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489876631325695518270963 2234814946988543277406445)
            ·
              refine ⟨838055605120703729027417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234814946988543277406445 838055605120703729027417)
              ·
                refine ⟨628541703840527796770563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838055605120703729027417 628541703840527796770563)
                ·
                  refine ⟨942812555760791695155845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628541703840527796770563 942812555760791695155845)
                  ·
                    refine ⟨176777354205148442841721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 942812555760791695155845 176777354205148442841721)
                    ·
                      rfl

theorem cell23_1032818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1032818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032818 prefixEnd_1032818 := by exact prefixLift 1032818
  have htrace : WordTrace (prefixWord ++ tailWord_1032818) baseStart_1032818 baseEnd_1032818 := by
    simpa [prefixWord, tailWord_1032818, baseEnd_1032818] using wordTrace_append hprefix tailTrace_1032818
  have hstable : (prefixWord ++ tailWord_1032818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032818).length < 2 ^ (prefixWord ++ tailWord_1032818).sum := by decide
  have hdescent : baseEnd_1032818 < baseStart_1032818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032894 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1032894 : Nat := 118140960795 + 1032894 * 2 ^ 59
def prefixEnd_1032894 : Nat := 4983230072969 + 3 ^ 40 * 1032894 * 2
def baseEnd_1032894 : Nat := 530371087145187031174813

theorem tailTrace_1032894 : CollatzResearch.WordTrace tailWord_1032894 prefixEnd_1032894 530371087145187031174813 := by
  unfold tailWord_1032894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709092390001114637006217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25115159413339278064033157 4709092390001114637006217)
  ·
    refine ⟨3531819292500835977754663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4709092390001114637006217 3531819292500835977754663)
    ·
      refine ⟨5297728938751253966631995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531819292500835977754663 5297728938751253966631995)
      ·
        refine ⟨7946593408126880949947993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297728938751253966631995 7946593408126880949947993)
        ·
          refine ⟨5959945056095160712460995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7946593408126880949947993 5959945056095160712460995)
          ·
            refine ⟨8939917584142741068691493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959945056095160712460995 8939917584142741068691493)
            ·
              refine ⟨1676234547026763950379655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8939917584142741068691493 1676234547026763950379655)
              ·
                refine ⟨2514351820540145925569483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676234547026763950379655 2514351820540145925569483)
                ·
                  refine ⟨3771527730810218888354225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514351820540145925569483 3771527730810218888354225)
                  ·
                    refine ⟨2828645798107664166265669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771527730810218888354225 2828645798107664166265669)
                    ·
                      refine ⟨530371087145187031174813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2828645798107664166265669 530371087145187031174813)
                      ·
                        rfl

theorem cell23_1032894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1032894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032894 prefixEnd_1032894 := by exact prefixLift 1032894
  have htrace : WordTrace (prefixWord ++ tailWord_1032894) baseStart_1032894 baseEnd_1032894 := by
    simpa [prefixWord, tailWord_1032894, baseEnd_1032894] using wordTrace_append hprefix tailTrace_1032894
  have hstable : (prefixWord ++ tailWord_1032894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032894).length < 2 ^ (prefixWord ++ tailWord_1032894).sum := by decide
  have hdescent : baseEnd_1032894 < baseStart_1032894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032902 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1032902 : Nat := 118140960795 + 1032902 * 2 ^ 59
def prefixEnd_1032902 : Nat := 4983230072969 + 3 ^ 40 * 1032902 * 2
def baseEnd_1032902 : Nat := 530375194990422999874777

theorem tailTrace_1032902 : CollatzResearch.WordTrace tailWord_1032902 prefixEnd_1032902 530375194990422999874777 := by
  unfold tailWord_1032902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177282215749372951948155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25115353935986622974893973 1177282215749372951948155)
  ·
    refine ⟨1765923323624059427922233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177282215749372951948155 1765923323624059427922233)
    ·
      refine ⟨1324442492718044570941675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765923323624059427922233 1324442492718044570941675)
      ·
        refine ⟨1986663739077066856412513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324442492718044570941675 1986663739077066856412513)
        ·
          refine ⟨1489997804307800142309385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1986663739077066856412513 1489997804307800142309385)
          ·
            refine ⟨1117498353230850106732039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489997804307800142309385 1117498353230850106732039)
            ·
              refine ⟨1676247529846275160098059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117498353230850106732039 1676247529846275160098059)
              ·
                refine ⟨2514371294769412740147089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676247529846275160098059 2514371294769412740147089)
                ·
                  refine ⟨1885778471077059555110317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514371294769412740147089 1885778471077059555110317)
                  ·
                    refine ⟨707166926653897333166369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885778471077059555110317 707166926653897333166369)
                    ·
                      refine ⟨530375194990422999874777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707166926653897333166369 530375194990422999874777)
                      ·
                        rfl

theorem cell23_1032902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1032902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032902 prefixEnd_1032902 := by exact prefixLift 1032902
  have htrace : WordTrace (prefixWord ++ tailWord_1032902) baseStart_1032902 baseEnd_1032902 := by
    simpa [prefixWord, tailWord_1032902, baseEnd_1032902] using wordTrace_append hprefix tailTrace_1032902
  have hstable : (prefixWord ++ tailWord_1032902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032902).length < 2 ^ (prefixWord ++ tailWord_1032902).sum := by decide
  have hdescent : baseEnd_1032902 < baseStart_1032902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032931 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1032931 : Nat := 118140960795 + 1032931 * 2 ^ 59
def prefixEnd_1032931 : Nat := 4983230072969 + 3 ^ 40 * 1032931 * 2
def baseEnd_1032931 : Nat := 530390085929403386412143

theorem tailTrace_1032931 : CollatzResearch.WordTrace tailWord_1032931 prefixEnd_1032931 530390085929403386412143 := by
  unfold tailWord_1032931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37674088620874872415146647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25116059080583248276764431 37674088620874872415146647)
  ·
    refine ⟨56511132931312308622719971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37674088620874872415146647 56511132931312308622719971)
    ·
      refine ⟨84766699396968462934079957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56511132931312308622719971 84766699396968462934079957)
      ·
        refine ⟨1986719517116448350017499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84766699396968462934079957 1986719517116448350017499)
        ·
          refine ⟨2980079275674672525026249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986719517116448350017499 2980079275674672525026249)
          ·
            refine ⟨2235059456756004393769687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980079275674672525026249 2235059456756004393769687)
            ·
              refine ⟨3352589185134006590654531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235059456756004393769687 3352589185134006590654531)
              ·
                refine ⟨5028883777701009885981797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352589185134006590654531 5028883777701009885981797)
                ·
                  refine ⟨942915708318939353621587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5028883777701009885981797 942915708318939353621587)
                  ·
                    refine ⟨1414373562478409030432381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 942915708318939353621587 1414373562478409030432381)
                    ·
                      refine ⟨530390085929403386412143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414373562478409030432381 530390085929403386412143)
                      ·
                        rfl

theorem cell23_1032931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1032931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032931 prefixEnd_1032931 := by exact prefixLift 1032931
  have htrace : WordTrace (prefixWord ++ tailWord_1032931) baseStart_1032931 baseEnd_1032931 := by
    simpa [prefixWord, tailWord_1032931, baseEnd_1032931] using wordTrace_append hprefix tailTrace_1032931
  have hstable : (prefixWord ++ tailWord_1032931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032931).length < 2 ^ (prefixWord ++ tailWord_1032931).sum := by decide
  have hdescent : baseEnd_1032931 < baseStart_1032931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032957 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1032957 : Nat := 118140960795 + 1032957 * 2 ^ 59
def prefixEnd_1032957 : Nat := 4983230072969 + 3 ^ 40 * 1032957 * 2
def baseEnd_1032957 : Nat := 530403436426420284687023

theorem tailTrace_1032957 : CollatzResearch.WordTrace tailWord_1032957 prefixEnd_1032957 530403436426420284687023 := by
  unfold tailWord_1032957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37675036918780678855593125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25116691279187119237062083 37675036918780678855593125)
  ·
    refine ⟨7064069422271377285423711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37675036918780678855593125 7064069422271377285423711)
    ·
      refine ⟨10596104133407065928135567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064069422271377285423711 10596104133407065928135567)
      ·
        refine ⟨15894156200110598892203351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596104133407065928135567 15894156200110598892203351)
        ·
          refine ⟨23841234300165898338305027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894156200110598892203351 23841234300165898338305027)
          ·
            refine ⟨35761851450248847507457541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23841234300165898338305027 35761851450248847507457541)
            ·
              refine ⟨6705347146921658907648289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35761851450248847507457541 6705347146921658907648289)
              ·
                refine ⟨5029010360191244180736217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705347146921658907648289 5029010360191244180736217)
                ·
                  refine ⟨3771757770143433135552163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029010360191244180736217 3771757770143433135552163)
                  ·
                    refine ⟨5657636655215149703328245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3771757770143433135552163 5657636655215149703328245)
                    ·
                      refine ⟨530403436426420284687023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5657636655215149703328245 530403436426420284687023)
                      ·
                        rfl

theorem cell23_1032957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1032957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032957 prefixEnd_1032957 := by exact prefixLift 1032957
  have htrace : WordTrace (prefixWord ++ tailWord_1032957) baseStart_1032957 baseEnd_1032957 := by
    simpa [prefixWord, tailWord_1032957, baseEnd_1032957] using wordTrace_append hprefix tailTrace_1032957
  have hstable : (prefixWord ++ tailWord_1032957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032957).length < 2 ^ (prefixWord ++ tailWord_1032957).sum := by decide
  have hdescent : baseEnd_1032957 < baseStart_1032957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032958 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_1032958 : Nat := 118140960795 + 1032958 * 2 ^ 59
def prefixEnd_1032958 : Nat := 4983230072969 + 3 ^ 40 * 1032958 * 2
def baseEnd_1032958 : Nat := 530403949907074780774519

theorem tailTrace_1032958 : CollatzResearch.WordTrace tailWord_1032958 prefixEnd_1032958 530403949907074780774519 := by
  unfold tailWord_1032958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709384173972132003297441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25116715594518037350919685 4709384173972132003297441)
  ·
    refine ⟨3532038130479099002473081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4709384173972132003297441 3532038130479099002473081)
    ·
      refine ⟨2649028597859324251854811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3532038130479099002473081 2649028597859324251854811)
      ·
        refine ⟨3973542896788986377782217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649028597859324251854811 3973542896788986377782217)
        ·
          refine ⟨2980157172591739783336663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3973542896788986377782217 2980157172591739783336663)
          ·
            refine ⟨4470235758887609675004995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980157172591739783336663 4470235758887609675004995)
            ·
              refine ⟨6705353638331414512507493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470235758887609675004995 6705353638331414512507493)
              ·
                refine ⟨1257253807187140221095155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6705353638331414512507493 1257253807187140221095155)
                ·
                  refine ⟨1885880710780710331642733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257253807187140221095155 1885880710780710331642733)
                  ·
                    refine ⟨707205266542766374366025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885880710780710331642733 707205266542766374366025)
                    ·
                      refine ⟨530403949907074780774519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707205266542766374366025 530403949907074780774519)
                      ·
                        rfl

theorem cell23_1032958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_1032958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032958 prefixEnd_1032958 := by exact prefixLift 1032958
  have htrace : WordTrace (prefixWord ++ tailWord_1032958) baseStart_1032958 baseEnd_1032958 := by
    simpa [prefixWord, tailWord_1032958, baseEnd_1032958] using wordTrace_append hprefix tailTrace_1032958
  have hstable : (prefixWord ++ tailWord_1032958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032958).length < 2 ^ (prefixWord ++ tailWord_1032958).sum := by decide
  have hdescent : baseEnd_1032958 < baseStart_1032958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032994 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1032994 : Nat := 118140960795 + 1032994 * 2 ^ 59
def prefixEnd_1032994 : Nat := 4983230072969 + 3 ^ 40 * 1032994 * 2
def baseEnd_1032994 : Nat := 58935826134515182213817

theorem tailTrace_1032994 : CollatzResearch.WordTrace tailWord_1032994 prefixEnd_1032994 58935826134515182213817 := by
  unfold tailWord_1032994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9419096604911658543672509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25117590946431089449793357 9419096604911658543672509)
  ·
    refine ⟨3532161226841871953877191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9419096604911658543672509 3532161226841871953877191)
    ·
      refine ⟨5298241840262807930815787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532161226841871953877191 5298241840262807930815787)
      ·
        refine ⟨7947362760394211896223681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298241840262807930815787 7947362760394211896223681)
        ·
          refine ⟨5960522070295658922167761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7947362760394211896223681 5960522070295658922167761)
          ·
            refine ⟨4470391552721744191625821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5960522070295658922167761 4470391552721744191625821)
            ·
              refine ⟨1676396832270654071859683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470391552721744191625821 1676396832270654071859683)
              ·
                refine ⟨2514595248405981107789525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676396832270654071859683 2514595248405981107789525)
                ·
                  refine ⟨58935826134515182213817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2514595248405981107789525 58935826134515182213817)
                  ·
                    rfl

theorem cell23_1032994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1032994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1032994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1032994 prefixEnd_1032994 := by exact prefixLift 1032994
  have htrace : WordTrace (prefixWord ++ tailWord_1032994) baseStart_1032994 baseEnd_1032994 := by
    simpa [prefixWord, tailWord_1032994, baseEnd_1032994] using wordTrace_append hprefix tailTrace_1032994
  have hstable : (prefixWord ++ tailWord_1032994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032994).length < 2 ^ (prefixWord ++ tailWord_1032994).sum := by decide
  have hdescent : baseEnd_1032994 < baseStart_1032994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033057 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1033057 : Nat := 118140960795 + 1033057 * 2 ^ 59
def prefixEnd_1033057 : Nat := 4983230072969 + 3 ^ 40 * 1033057 * 2
def baseEnd_1033057 : Nat := 530454784491869893436563

theorem tailTrace_1033057 : CollatzResearch.WordTrace tailWord_1033057 prefixEnd_1033057 530454784491869893436563 := by
  unfold tailWord_1033057
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678684218418395934233425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25119122812278930622822283 37678684218418395934233425)
  ·
    refine ⟨28259013163813796950675069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37678684218418395934233425 28259013163813796950675069)
    ·
      refine ⟨10597129936430173856503151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28259013163813796950675069 10597129936430173856503151)
      ·
        refine ⟨15895694904645260784754727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10597129936430173856503151 15895694904645260784754727)
        ·
          refine ⟨23843542356967891177132091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895694904645260784754727 23843542356967891177132091)
          ·
            refine ⟨35765313535451836765698137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23843542356967891177132091 35765313535451836765698137)
            ·
              refine ⟨26823985151588877574273603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35765313535451836765698137 26823985151588877574273603)
              ·
                refine ⟨40235977727383316361410405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26823985151588877574273603 40235977727383316361410405)
                ·
                  refine ⟨7544245823884371817764451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40235977727383316361410405 7544245823884371817764451)
                  ·
                    refine ⟨11316368735826557726646677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544245823884371817764451 11316368735826557726646677)
                    ·
                      refine ⟨530454784491869893436563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11316368735826557726646677 530454784491869893436563)
                      ·
                        rfl

theorem cell23_1033057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1033057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033057 prefixEnd_1033057 := by exact prefixLift 1033057
  have htrace : WordTrace (prefixWord ++ tailWord_1033057) baseStart_1033057 baseEnd_1033057 := by
    simpa [prefixWord, tailWord_1033057, baseEnd_1033057] using wordTrace_append hprefix tailTrace_1033057
  have hstable : (prefixWord ++ tailWord_1033057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033057).length < 2 ^ (prefixWord ++ tailWord_1033057).sum := by decide
  have hdescent : baseEnd_1033057 < baseStart_1033057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033078 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1033078 : Nat := 118140960795 + 1033078 * 2 ^ 59
def prefixEnd_1033078 : Nat := 4983230072969 + 3 ^ 40 * 1033078 * 2
def baseEnd_1033078 : Nat := 530465567585614311273967

theorem tailTrace_1033078 : CollatzResearch.WordTrace tailWord_1033078 prefixEnd_1033078 530465567585614311273967 := by
  unfold tailWord_1033078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354965634458894782546743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25119633434228211013831925 2354965634458894782546743)
  ·
    refine ⟨3532448451688342173820115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2354965634458894782546743 3532448451688342173820115)
    ·
      refine ⟨5298672677532513260730173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532448451688342173820115 5298672677532513260730173)
      ·
        refine ⟨1987002254074692472773815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5298672677532513260730173 1987002254074692472773815)
        ·
          refine ⟨2980503381112038709160723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987002254074692472773815 2980503381112038709160723)
          ·
            refine ⟨4470755071668058063741085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980503381112038709160723 4470755071668058063741085)
            ·
              refine ⟨1676533151875521773902907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470755071668058063741085 1676533151875521773902907)
              ·
                refine ⟨2514799727813282660854361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676533151875521773902907 2514799727813282660854361)
                ·
                  refine ⟨1886099795859961995640771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514799727813282660854361 1886099795859961995640771)
                  ·
                    refine ⟨2829149693789942993461157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886099795859961995640771 2829149693789942993461157)
                    ·
                      refine ⟨530465567585614311273967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2829149693789942993461157 530465567585614311273967)
                      ·
                        rfl

theorem cell23_1033078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1033078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033078 prefixEnd_1033078 := by exact prefixLift 1033078
  have htrace : WordTrace (prefixWord ++ tailWord_1033078) baseStart_1033078 baseEnd_1033078 := by
    simpa [prefixWord, tailWord_1033078, baseEnd_1033078] using wordTrace_append hprefix tailTrace_1033078
  have hstable : (prefixWord ++ tailWord_1033078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033078).length < 2 ^ (prefixWord ++ tailWord_1033078).sum := by decide
  have hdescent : baseEnd_1033078 < baseStart_1033078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033081 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_1033081 : Nat := 118140960795 + 1033081 * 2 ^ 59
def prefixEnd_1033081 : Nat := 4983230072969 + 3 ^ 40 * 1033081 * 2
def baseEnd_1033081 : Nat := 530467108027577799536453

theorem tailTrace_1033081 : CollatzResearch.WordTrace tailWord_1033081 prefixEnd_1033081 530467108027577799536453 := by
  unfold tailWord_1033081
  simp only [CollatzResearch.WordTrace]
  refine ⟨37679559570331448033107097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25119706380220965355404731 37679559570331448033107097)
  ·
    refine ⟨28259669677748586024830323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37679559570331448033107097 28259669677748586024830323)
    ·
      refine ⟨42389504516622879037245485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28259669677748586024830323 42389504516622879037245485)
      ·
        refine ⟨15896064193733579638967057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42389504516622879037245485 15896064193733579638967057)
        ·
          refine ⟨11922048145300184729225293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15896064193733579638967057 11922048145300184729225293)
          ·
            refine ⟨4470768054487569273459485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11922048145300184729225293 4470768054487569273459485)
            ·
              refine ⟨1676538020432838477547307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470768054487569273459485 1676538020432838477547307)
              ·
                refine ⟨2514807030649257716320961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676538020432838477547307 2514807030649257716320961)
                ·
                  refine ⟨1886105272986943287240721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514807030649257716320961 1886105272986943287240721)
                  ·
                    refine ⟨1414578954740207465430541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1886105272986943287240721 1414578954740207465430541)
                    ·
                      refine ⟨530467108027577799536453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414578954740207465430541 530467108027577799536453)
                      ·
                        rfl

theorem cell23_1033081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_1033081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033081 prefixEnd_1033081 := by exact prefixLift 1033081
  have htrace : WordTrace (prefixWord ++ tailWord_1033081) baseStart_1033081 baseEnd_1033081 := by
    simpa [prefixWord, tailWord_1033081, baseEnd_1033081] using wordTrace_append hprefix tailTrace_1033081
  have hstable : (prefixWord ++ tailWord_1033081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033081).length < 2 ^ (prefixWord ++ tailWord_1033081).sum := by decide
  have hdescent : baseEnd_1033081 < baseStart_1033081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033107 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1033107 : Nat := 118140960795 + 1033107 * 2 ^ 59
def prefixEnd_1033107 : Nat := 4983230072969 + 3 ^ 40 * 1033107 * 2
def baseEnd_1033107 : Nat := 530480458524594697811333

theorem tailTrace_1033107 : CollatzResearch.WordTrace tailWord_1033107 prefixEnd_1033107 530480458524594697811333 := by
  unfold tailWord_1033107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680507868237254473553575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25120338578824836315702383 37680507868237254473553575)
  ·
    refine ⟨56520761802355881710330363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37680507868237254473553575 56520761802355881710330363)
    ·
      refine ⟨84781142703533822565495545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56520761802355881710330363 84781142703533822565495545)
      ·
        refine ⟨63585857027650366924121659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84781142703533822565495545 63585857027650366924121659)
        ·
          refine ⟨95378785541475550386182489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63585857027650366924121659 95378785541475550386182489)
          ·
            refine ⟨71534089156106662789636867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95378785541475550386182489 71534089156106662789636867)
            ·
              refine ⟨107301133734159994184455301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71534089156106662789636867 107301133734159994184455301)
              ·
                refine ⟨20118962575154998909585369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107301133734159994184455301 20118962575154998909585369)
                ·
                  refine ⟨15089221931366249182189027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118962575154998909585369 15089221931366249182189027)
                  ·
                    refine ⟨22633832897049373773283541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15089221931366249182189027 22633832897049373773283541)
                    ·
                      refine ⟨530480458524594697811333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22633832897049373773283541 530480458524594697811333)
                      ·
                        rfl

theorem cell23_1033107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1033107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033107 prefixEnd_1033107 := by exact prefixLift 1033107
  have htrace : WordTrace (prefixWord ++ tailWord_1033107) baseStart_1033107 baseEnd_1033107 := by
    simpa [prefixWord, tailWord_1033107, baseEnd_1033107] using wordTrace_append hprefix tailTrace_1033107
  have hstable : (prefixWord ++ tailWord_1033107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033107).length < 2 ^ (prefixWord ++ tailWord_1033107).sum := by decide
  have hdescent : baseEnd_1033107 < baseStart_1033107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033145 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1033145 : Nat := 118140960795 + 1033145 * 2 ^ 59
def prefixEnd_1033145 : Nat := 4983230072969 + 3 ^ 40 * 1033145 * 2
def baseEnd_1033145 : Nat := 530499970789465549136159

theorem tailTrace_1033145 : CollatzResearch.WordTrace tailWord_1033145 prefixEnd_1033145 530499970789465549136159 := by
  unfold tailWord_1033145
  simp only [CollatzResearch.WordTrace]
  refine ⟨37681893842099586963436889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25121262561399724642291259 37681893842099586963436889)
  ·
    refine ⟨28261420381574690222577667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37681893842099586963436889 28261420381574690222577667)
    ·
      refine ⟨42392130572362035333866501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28261420381574690222577667 42392130572362035333866501)
      ·
        refine ⟨7948524482317881625099969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42392130572362035333866501 7948524482317881625099969)
        ·
          refine ⟨5961393361738411218824977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948524482317881625099969 5961393361738411218824977)
          ·
            refine ⟨4471045021303808414118733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5961393361738411218824977 4471045021303808414118733)
            ·
              refine ⟨1676641882988928155294525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471045021303808414118733 1676641882988928155294525)
              ·
                refine ⟨628740706120848058235447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676641882988928155294525 628740706120848058235447)
                ·
                  refine ⟨943111059181272087353171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628740706120848058235447 943111059181272087353171)
                  ·
                    refine ⟨1414666588771908131029757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943111059181272087353171 1414666588771908131029757)
                    ·
                      refine ⟨530499970789465549136159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414666588771908131029757 530499970789465549136159)
                      ·
                        rfl

theorem cell23_1033145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1033145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033145 prefixEnd_1033145 := by exact prefixLift 1033145
  have htrace : WordTrace (prefixWord ++ tailWord_1033145) baseStart_1033145 baseEnd_1033145 := by
    simpa [prefixWord, tailWord_1033145, baseEnd_1033145] using wordTrace_append hprefix tailTrace_1033145
  have hstable : (prefixWord ++ tailWord_1033145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033145).length < 2 ^ (prefixWord ++ tailWord_1033145).sum := by decide
  have hdescent : baseEnd_1033145 < baseStart_1033145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033164 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1033164 : Nat := 118140960795 + 1033164 * 2 ^ 59
def prefixEnd_1033164 : Nat := 4983230072969 + 3 ^ 40 * 1033164 * 2
def baseEnd_1033164 : Nat := 530509726921900974798571

theorem tailTrace_1033164 : CollatzResearch.WordTrace tailWord_1033164 prefixEnd_1033164 530509726921900974798571 := by
  unfold tailWord_1033164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841293414515376604189273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25121724552687168805585697 18841293414515376604189273)
  ·
    refine ⟨14130970060886532453141955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18841293414515376604189273 14130970060886532453141955)
    ·
      refine ⟨21196455091329798679712933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14130970060886532453141955 21196455091329798679712933)
      ·
        refine ⟨3974335329624337252446175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21196455091329798679712933 3974335329624337252446175)
        ·
          refine ⟨5961502994436505878669263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974335329624337252446175 5961502994436505878669263)
          ·
            refine ⟨8942254491654758818003895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961502994436505878669263 8942254491654758818003895)
            ·
              refine ⟨13413381737482138227005843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942254491654758818003895 13413381737482138227005843)
              ·
                refine ⟨20120072606223207340508765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413381737482138227005843 20120072606223207340508765)
                ·
                  refine ⟨7545027227333702752690787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20120072606223207340508765 7545027227333702752690787)
                  ·
                    refine ⟨11317540841000554129036181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545027227333702752690787 11317540841000554129036181)
                    ·
                      refine ⟨530509726921900974798571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11317540841000554129036181 530509726921900974798571)
                      ·
                        rfl

theorem cell23_1033164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1033164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033164 prefixEnd_1033164 := by exact prefixLift 1033164
  have htrace : WordTrace (prefixWord ++ tailWord_1033164) baseStart_1033164 baseEnd_1033164 := by
    simpa [prefixWord, tailWord_1033164, baseEnd_1033164] using wordTrace_append hprefix tailTrace_1033164
  have hstable : (prefixWord ++ tailWord_1033164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033164).length < 2 ^ (prefixWord ++ tailWord_1033164).sum := by decide
  have hdescent : baseEnd_1033164 < baseStart_1033164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033178 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_1033178 : Nat := 118140960795 + 1033178 * 2 ^ 59
def prefixEnd_1033178 : Nat := 4983230072969 + 3 ^ 40 * 1033178 * 2
def baseEnd_1033178 : Nat := 176838971883687973341169

theorem tailTrace_1033178 : CollatzResearch.WordTrace tailWord_1033178 prefixEnd_1033178 176838971883687973341169 := by
  unfold tailWord_1033178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420774362745008399847047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25122064967320022399592125 9420774362745008399847047)
  ·
    refine ⟨14131161544117512599770571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9420774362745008399847047 14131161544117512599770571)
    ·
      refine ⟨21196742316176268899655857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131161544117512599770571 21196742316176268899655857)
      ·
        refine ⟨15897556737132201674741893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21196742316176268899655857 15897556737132201674741893)
        ·
          refine ⟨2980791888212287814014105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15897556737132201674741893 2980791888212287814014105)
          ·
            refine ⟨2235593916159215860510579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980791888212287814014105 2235593916159215860510579)
            ·
              refine ⟨3353390874238823790765869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235593916159215860510579 3353390874238823790765869)
              ·
                refine ⟨1257521577839558921537201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3353390874238823790765869 1257521577839558921537201)
                ·
                  refine ⟨943141183379669191152901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257521577839558921537201 943141183379669191152901)
                  ·
                    refine ⟨176838971883687973341169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943141183379669191152901 176838971883687973341169)
                    ·
                      rfl

theorem cell23_1033178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_1033178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033178 prefixEnd_1033178 := by exact prefixLift 1033178
  have htrace : WordTrace (prefixWord ++ tailWord_1033178) baseStart_1033178 baseEnd_1033178 := by
    simpa [prefixWord, tailWord_1033178, baseEnd_1033178] using wordTrace_append hprefix tailTrace_1033178
  have hstable : (prefixWord ++ tailWord_1033178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033178).length < 2 ^ (prefixWord ++ tailWord_1033178).sum := by decide
  have hdescent : baseEnd_1033178 < baseStart_1033178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033181 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1033181 : Nat := 118140960795 + 1033181 * 2 ^ 59
def prefixEnd_1033181 : Nat := 4983230072969 + 3 ^ 40 * 1033181 * 2
def baseEnd_1033181 : Nat := 530518456093027408285993

theorem tailTrace_1033181 : CollatzResearch.WordTrace tailWord_1033181 prefixEnd_1033181 530518456093027408285993 := by
  unfold tailWord_1033181
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683206869969165111747397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25122137913312776741164931 37683206869969165111747397)
  ·
    refine ⟨7065601288119218458452637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37683206869969165111747397 7065601288119218458452637)
    ·
      refine ⟨2649600483044706921919739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7065601288119218458452637 2649600483044706921919739)
      ·
        refine ⟨3974400724567060382879609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649600483044706921919739 3974400724567060382879609)
        ·
          refine ⟨2980800543425295287159707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974400724567060382879609 2980800543425295287159707)
          ·
            refine ⟨4471200815137942930739561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980800543425295287159707 4471200815137942930739561)
            ·
              refine ⟨3353400611353457198054671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4471200815137942930739561 3353400611353457198054671)
              ·
                refine ⟨5030100917030185797082007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353400611353457198054671 5030100917030185797082007)
                ·
                  refine ⟨7545151375545278695623011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030100917030185797082007 7545151375545278695623011)
                  ·
                    refine ⟨11317727063317918043434517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545151375545278695623011 11317727063317918043434517)
                    ·
                      refine ⟨530518456093027408285993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11317727063317918043434517 530518456093027408285993)
                      ·
                        rfl

theorem cell23_1033181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1033181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033181 prefixEnd_1033181 := by exact prefixLift 1033181
  have htrace : WordTrace (prefixWord ++ tailWord_1033181) baseStart_1033181 baseEnd_1033181 := by
    simpa [prefixWord, tailWord_1033181, baseEnd_1033181] using wordTrace_append hprefix tailTrace_1033181
  have hstable : (prefixWord ++ tailWord_1033181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033181).length < 2 ^ (prefixWord ++ tailWord_1033181).sum := by decide
  have hdescent : baseEnd_1033181 < baseStart_1033181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033198 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1033198 : Nat := 118140960795 + 1033198 * 2 ^ 59
def prefixEnd_1033198 : Nat := 4983230072969 + 3 ^ 40 * 1033198 * 2
def baseEnd_1033198 : Nat := 530527185264153841773415

theorem tailTrace_1033198 : CollatzResearch.WordTrace tailWord_1033198 prefixEnd_1033198 530527185264153841773415 := by
  unfold tailWord_1033198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710478363863447126889531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25122551273938384676744165 4710478363863447126889531)
  ·
    refine ⟨7065717545795170690334297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4710478363863447126889531 7065717545795170690334297)
    ·
      refine ⟨5299288159346378017750723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7065717545795170690334297 5299288159346378017750723)
      ·
        refine ⟨7948932239019567026626085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299288159346378017750723 7948932239019567026626085)
        ·
          refine ⟨1490424794816168817492391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7948932239019567026626085 1490424794816168817492391)
          ·
            refine ⟨2235637192224253226238587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490424794816168817492391 2235637192224253226238587)
            ·
              refine ⟨3353455788336379839357881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235637192224253226238587 3353455788336379839357881)
              ·
                refine ⟨2515091841252284879518411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353455788336379839357881 2515091841252284879518411)
                ·
                  refine ⟨3772637761878427319277617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515091841252284879518411 3772637761878427319277617)
                  ·
                    refine ⟨2829478321408820489458213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772637761878427319277617 2829478321408820489458213)
                    ·
                      refine ⟨530527185264153841773415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2829478321408820489458213 530527185264153841773415)
                      ·
                        rfl

theorem cell23_1033198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1033198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033198 prefixEnd_1033198 := by exact prefixLift 1033198
  have htrace : WordTrace (prefixWord ++ tailWord_1033198) baseStart_1033198 baseEnd_1033198 := by
    simpa [prefixWord, tailWord_1033198, baseEnd_1033198] using wordTrace_append hprefix tailTrace_1033198
  have hstable : (prefixWord ++ tailWord_1033198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033198).length < 2 ^ (prefixWord ++ tailWord_1033198).sum := by decide
  have hdescent : baseEnd_1033198 < baseStart_1033198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033201 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_1033201 : Nat := 118140960795 + 1033201 * 2 ^ 59
def prefixEnd_1033201 : Nat := 4983230072969 + 3 ^ 40 * 1033201 * 2
def baseEnd_1033201 : Nat := 530528725706117330035901

theorem tailTrace_1033201 : CollatzResearch.WordTrace tailWord_1033201 prefixEnd_1033201 530528725706117330035901 := by
  unfold tailWord_1033201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683936329896708527475457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25122624219931139018316971 37683936329896708527475457)
  ·
    refine ⟨28262952247422531395606593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37683936329896708527475457 28262952247422531395606593)
    ·
      refine ⟨21197214185566898546704945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28262952247422531395606593 21197214185566898546704945)
      ·
        refine ⟨15897910639175173910028709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21197214185566898546704945 15897910639175173910028709)
        ·
          refine ⟨2980858244845345108130383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15897910639175173910028709 2980858244845345108130383)
          ·
            refine ⟨4471287367268017662195575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980858244845345108130383 4471287367268017662195575)
            ·
              refine ⟨6706931050902026493293363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471287367268017662195575 6706931050902026493293363)
              ·
                refine ⟨10060396576353039739940045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706931050902026493293363 10060396576353039739940045)
                ·
                  refine ⟨3772648716132389902477517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10060396576353039739940045 3772648716132389902477517)
                  ·
                    refine ⟨1414743268549646213429069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772648716132389902477517 1414743268549646213429069)
                    ·
                      refine ⟨530528725706117330035901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1414743268549646213429069 530528725706117330035901)
                      ·
                        rfl

theorem cell23_1033201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_1033201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033201 prefixEnd_1033201 := by exact prefixLift 1033201
  have htrace : WordTrace (prefixWord ++ tailWord_1033201) baseStart_1033201 baseEnd_1033201 := by
    simpa [prefixWord, tailWord_1033201, baseEnd_1033201] using wordTrace_append hprefix tailTrace_1033201
  have hstable : (prefixWord ++ tailWord_1033201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033201).length < 2 ^ (prefixWord ++ tailWord_1033201).sum := by decide
  have hdescent : baseEnd_1033201 < baseStart_1033201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033202 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1033202 : Nat := 118140960795 + 1033202 * 2 ^ 59
def prefixEnd_1033202 : Nat := 4983230072969 + 3 ^ 40 * 1033202 * 2
def baseEnd_1033202 : Nat := 530529239186771826123397

theorem tailTrace_1033202 : CollatzResearch.WordTrace tailWord_1033202 prefixEnd_1033202 530529239186771826123397 := by
  unfold tailWord_1033202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420993200723271424565465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25122648535262057132174573 9420993200723271424565465)
  ·
    refine ⟨7065744900542453568424099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9420993200723271424565465 7065744900542453568424099)
    ·
      refine ⟨10598617350813680352636149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7065744900542453568424099 10598617350813680352636149)
      ·
        refine ⟨993620376638782533059639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10598617350813680352636149 993620376638782533059639)
        ·
          refine ⟨1490430564958173799589459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993620376638782533059639 1490430564958173799589459)
          ·
            refine ⟨2235645847437260699384189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490430564958173799589459 2235645847437260699384189)
            ·
              refine ⟨838367192788972762269071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2235645847437260699384189 838367192788972762269071)
              ·
                refine ⟨1257550789183459143403607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838367192788972762269071 1257550789183459143403607)
                ·
                  refine ⟨1886326183775188715105411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257550789183459143403607 1886326183775188715105411)
                  ·
                    refine ⟨2829489275662783072658117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886326183775188715105411 2829489275662783072658117)
                    ·
                      refine ⟨530529239186771826123397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2829489275662783072658117 530529239186771826123397)
                      ·
                        rfl

theorem cell23_1033202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1033202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033202 prefixEnd_1033202 := by exact prefixLift 1033202
  have htrace : WordTrace (prefixWord ++ tailWord_1033202) baseStart_1033202 baseEnd_1033202 := by
    simpa [prefixWord, tailWord_1033202, baseEnd_1033202] using wordTrace_append hprefix tailTrace_1033202
  have hstable : (prefixWord ++ tailWord_1033202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033202).length < 2 ^ (prefixWord ++ tailWord_1033202).sum := by decide
  have hdescent : baseEnd_1033202 < baseStart_1033202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033228 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_1033228 : Nat := 118140960795 + 1033228 * 2 ^ 59
def prefixEnd_1033228 : Nat := 4983230072969 + 3 ^ 40 * 1033228 * 2
def baseEnd_1033228 : Nat := 530542589683788724398277

theorem tailTrace_1033228 : CollatzResearch.WordTrace tailWord_1033228 prefixEnd_1033228 530542589683788724398277 := by
  unfold tailWord_1033228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842460550399446069354169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25123280733865928092472225 18842460550399446069354169)
  ·
    refine ⟨14131845412799584552015627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18842460550399446069354169 14131845412799584552015627)
    ·
      refine ⟨21197768119199376828023441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131845412799584552015627 21197768119199376828023441)
      ·
        refine ⟨15898326089399532621017581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21197768119199376828023441 15898326089399532621017581)
        ·
          refine ⟨5961872283524824732881593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15898326089399532621017581 5961872283524824732881593)
          ·
            refine ⟨4471404212643618549661195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5961872283524824732881593 4471404212643618549661195)
            ·
              refine ⟨6707106318965427824491793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471404212643618549661195 6707106318965427824491793)
              ·
                refine ⟨5030329739224070868368845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707106318965427824491793 5030329739224070868368845)
                ·
                  refine ⟨1886373652209026575638317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5030329739224070868368845 1886373652209026575638317)
                  ·
                    refine ⟨707390119578384965864369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886373652209026575638317 707390119578384965864369)
                    ·
                      refine ⟨530542589683788724398277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707390119578384965864369 530542589683788724398277)
                      ·
                        rfl

theorem cell23_1033228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_1033228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033228 prefixEnd_1033228 := by exact prefixLift 1033228
  have htrace : WordTrace (prefixWord ++ tailWord_1033228) baseStart_1033228 baseEnd_1033228 := by
    simpa [prefixWord, tailWord_1033228, baseEnd_1033228] using wordTrace_append hprefix tailTrace_1033228
  have hstable : (prefixWord ++ tailWord_1033228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033228).length < 2 ^ (prefixWord ++ tailWord_1033228).sum := by decide
  have hdescent : baseEnd_1033228 < baseStart_1033228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033264 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 9]
def baseStart_1033264 : Nat := 118140960795 + 1033264 * 2 ^ 59
def prefixEnd_1033264 : Nat := 4983230072969 + 3 ^ 40 * 1033264 * 2
def baseEnd_1033264 : Nat := 58951230554150064838679

theorem tailTrace_1033264 : CollatzResearch.WordTrace tailWord_1033264 prefixEnd_1033264 58951230554150064838679 := by
  unfold tailWord_1033264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843117064334235143509423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25124156085778980191345897 18843117064334235143509423)
  ·
    refine ⟨28264675596501352715264135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18843117064334235143509423 28264675596501352715264135)
    ·
      refine ⟨42397013394752029072896203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28264675596501352715264135 42397013394752029072896203)
      ·
        refine ⟨63595520092128043609344305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42397013394752029072896203 63595520092128043609344305)
        ·
          refine ⟨47696640069096032707008229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63595520092128043609344305 47696640069096032707008229)
          ·
            refine ⟨8943120012955506132564043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47696640069096032707008229 8943120012955506132564043)
            ·
              refine ⟨13414680019433259198846065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943120012955506132564043 13414680019433259198846065)
              ·
                refine ⟨10061010014574944399134549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13414680019433259198846065 10061010014574944399134549)
                ·
                  refine ⟨58951230554150064838679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10061010014574944399134549 58951230554150064838679)
                  ·
                    rfl

theorem cell23_1033264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_1033264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033264 prefixEnd_1033264 := by exact prefixLift 1033264
  have htrace : WordTrace (prefixWord ++ tailWord_1033264) baseStart_1033264 baseEnd_1033264 := by
    simpa [prefixWord, tailWord_1033264, baseEnd_1033264] using wordTrace_append hprefix tailTrace_1033264
  have hstable : (prefixWord ++ tailWord_1033264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033264).length < 2 ^ (prefixWord ++ tailWord_1033264).sum := by decide
  have hdescent : baseEnd_1033264 < baseStart_1033264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033268 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1033268 : Nat := 118140960795 + 1033268 * 2 ^ 59
def prefixEnd_1033268 : Nat := 4983230072969 + 3 ^ 40 * 1033268 * 2
def baseEnd_1033268 : Nat := 176854376303322855966031

theorem tailTrace_1033268 : CollatzResearch.WordTrace tailWord_1033268 prefixEnd_1033268 176854376303322855966031 := by
  unfold tailWord_1033268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843190010326989485082229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25124253347102652646776305 18843190010326989485082229)
  ·
    refine ⟨1766549063468155264226459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18843190010326989485082229 1766549063468155264226459)
    ·
      refine ⟨2649823595202232896339689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766549063468155264226459 2649823595202232896339689)
      ·
        refine ⟨1987367696401674672254767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649823595202232896339689 1987367696401674672254767)
        ·
          refine ⟨2981051544602512008382151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987367696401674672254767 2981051544602512008382151)
          ·
            refine ⟨4471577316903768012573227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981051544602512008382151 4471577316903768012573227)
            ·
              refine ⟨6707365975355652018859841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471577316903768012573227 6707365975355652018859841)
              ·
                refine ⟨5030524481516739014144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707365975355652018859841 5030524481516739014144881)
                ·
                  refine ⟨3772893361137554260608661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030524481516739014144881 3772893361137554260608661)
                  ·
                    refine ⟨176854376303322855966031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3772893361137554260608661 176854376303322855966031)
                    ·
                      rfl

theorem cell23_1033268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1033268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033268 prefixEnd_1033268 := by exact prefixLift 1033268
  have htrace : WordTrace (prefixWord ++ tailWord_1033268) baseStart_1033268 baseEnd_1033268 := by
    simpa [prefixWord, tailWord_1033268, baseEnd_1033268] using wordTrace_append hprefix tailTrace_1033268
  have hstable : (prefixWord ++ tailWord_1033268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033268).length < 2 ^ (prefixWord ++ tailWord_1033268).sum := by decide
  have hdescent : baseEnd_1033268 < baseStart_1033268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033311 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 2, 5]
def baseStart_1033311 : Nat := 118140960795 + 1033311 * 2 ^ 59
def prefixEnd_1033311 : Nat := 4983230072969 + 3 ^ 40 * 1033311 * 2
def baseEnd_1033311 : Nat := 176861736192703966553465

theorem tailTrace_1033311 : CollatzResearch.WordTrace tailWord_1033311 prefixEnd_1033311 176861736192703966553465 := by
  unfold tailWord_1033311
  simp only [CollatzResearch.WordTrace]
  refine ⟨37687948359498197313979787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25125298906332131542653191 37687948359498197313979787)
  ·
    refine ⟨56531922539247295970969681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37687948359498197313979787 56531922539247295970969681)
    ·
      refine ⟨42398941904435471978227261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56531922539247295970969681 42398941904435471978227261)
      ·
        refine ⟨15899603214163301991835223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42398941904435471978227261 15899603214163301991835223)
        ·
          refine ⟨23849404821244952987752835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15899603214163301991835223 23849404821244952987752835)
          ·
            refine ⟨35774107231867429481629253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849404821244952987752835 35774107231867429481629253)
            ·
              refine ⟨6707645105975143027805485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35774107231867429481629253 6707645105975143027805485)
              ·
                refine ⟨2515366914740678635427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707645105975143027805485 2515366914740678635427057)
                ·
                  refine ⟨1886525186055508976570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515366914740678635427057 1886525186055508976570293)
                  ·
                    refine ⟨176861736192703966553465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1886525186055508976570293 176861736192703966553465)
                    ·
                      rfl

theorem cell23_1033311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_1033311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033311 prefixEnd_1033311 := by exact prefixLift 1033311
  have htrace : WordTrace (prefixWord ++ tailWord_1033311) baseStart_1033311 baseEnd_1033311 := by
    simpa [prefixWord, tailWord_1033311, baseEnd_1033311] using wordTrace_append hprefix tailTrace_1033311
  have hstable : (prefixWord ++ tailWord_1033311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033311).length < 2 ^ (prefixWord ++ tailWord_1033311).sum := by decide
  have hdescent : baseEnd_1033311 < baseStart_1033311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033418 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1033418 : Nat := 118140960795 + 1033418 * 2 ^ 59
def prefixEnd_1033418 : Nat := 4983230072969 + 3 ^ 40 * 1033418 * 2
def baseEnd_1033418 : Nat := 176880050336047660340801

theorem tailTrace_1033418 : CollatzResearch.WordTrace tailWord_1033418 prefixEnd_1033418 176880050336047660340801 := by
  unfold tailWord_1033418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422962742527638647031227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25127900646740369725416605 9422962742527638647031227)
  ·
    refine ⟨14134444113791457970546841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422962742527638647031227 14134444113791457970546841)
    ·
      refine ⟨10600833085343593477910131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14134444113791457970546841 10600833085343593477910131)
      ·
        refine ⟨15901249628015390216865197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600833085343593477910131 15901249628015390216865197)
        ·
          refine ⟨5962968610505771331324449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15901249628015390216865197 5962968610505771331324449)
          ·
            refine ⟨4472226457879328498493337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962968610505771331324449 4472226457879328498493337)
            ·
              refine ⟨3354169843409496373870003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472226457879328498493337 3354169843409496373870003)
              ·
                refine ⟨5031254765114244560805005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354169843409496373870003 5031254765114244560805005)
                ·
                  refine ⟨1886720536917841710301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5031254765114244560805005 1886720536917841710301877)
                  ·
                    refine ⟨176880050336047660340801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1886720536917841710301877 176880050336047660340801)
                    ·
                      rfl

theorem cell23_1033418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1033418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033418 prefixEnd_1033418 := by exact prefixLift 1033418
  have htrace : WordTrace (prefixWord ++ tailWord_1033418) baseStart_1033418 baseEnd_1033418 := by
    simpa [prefixWord, tailWord_1033418, baseEnd_1033418] using wordTrace_append hprefix tailTrace_1033418
  have hstable : (prefixWord ++ tailWord_1033418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033418).length < 2 ^ (prefixWord ++ tailWord_1033418).sum := by decide
  have hdescent : baseEnd_1033418 < baseStart_1033418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033475 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 3]
def baseStart_1033475 : Nat := 118140960795 + 1033475 * 2 ^ 59
def prefixEnd_1033475 : Nat := 4983230072969 + 3 ^ 40 * 1033475 * 2
def baseEnd_1033475 : Nat := 530669419405449258009641

theorem tailTrace_1033475 : CollatzResearch.WordTrace tailWord_1033475 prefixEnd_1033475 530669419405449258009641 := by
  unfold tailWord_1033475
  simp only [CollatzResearch.WordTrace]
  refine ⟨37693929930904053322949879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25129286620602702215299919 37693929930904053322949879)
  ·
    refine ⟨56540894896356079984424819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37693929930904053322949879 56540894896356079984424819)
    ·
      refine ⟨84811342344534119976637229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56540894896356079984424819 84811342344534119976637229)
      ·
        refine ⟨31804253379200294991238961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84811342344534119976637229 31804253379200294991238961)
        ·
          refine ⟨23853190034400221243429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31804253379200294991238961 23853190034400221243429221)
          ·
            refine ⟨4472473131450041483142979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23853190034400221243429221 4472473131450041483142979)
            ·
              refine ⟨6708709697175062224714469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472473131450041483142979 6708709697175062224714469)
              ·
                refine ⟨1257883068220324167133963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6708709697175062224714469 1257883068220324167133963)
                ·
                  refine ⟨1886824602330486250700945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257883068220324167133963 1886824602330486250700945)
                  ·
                    refine ⟨1415118451747864688025709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1886824602330486250700945 1415118451747864688025709)
                    ·
                      refine ⟨530669419405449258009641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415118451747864688025709 530669419405449258009641)
                      ·
                        rfl

theorem cell23_1033475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_1033475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033475 prefixEnd_1033475 := by exact prefixLift 1033475
  have htrace : WordTrace (prefixWord ++ tailWord_1033475) baseStart_1033475 baseEnd_1033475 := by
    simpa [prefixWord, tailWord_1033475, baseEnd_1033475] using wordTrace_append hprefix tailTrace_1033475
  have hstable : (prefixWord ++ tailWord_1033475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033475).length < 2 ^ (prefixWord ++ tailWord_1033475).sum := by decide
  have hdescent : baseEnd_1033475 < baseStart_1033475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033491 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 9]
def baseStart_1033491 : Nat := 118140960795 + 1033491 * 2 ^ 59
def prefixEnd_1033491 : Nat := 4983230072969 + 3 ^ 40 * 1033491 * 2
def baseEnd_1033491 : Nat := 176892545031973731803189

theorem tailTrace_1033491 : CollatzResearch.WordTrace tailWord_1033491 prefixEnd_1033491 176892545031973731803189 := by
  unfold tailWord_1033491
  simp only [CollatzResearch.WordTrace]
  refine ⟨37694513498846088055532327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25129675665897392037021551 37694513498846088055532327)
  ·
    refine ⟨56541770248269132083298491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37694513498846088055532327 56541770248269132083298491)
    ·
      refine ⟨84812655372403698124947737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56541770248269132083298491 84812655372403698124947737)
      ·
        refine ⟨63609491529302773593710803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84812655372403698124947737 63609491529302773593710803)
        ·
          refine ⟨95414237293954160390566205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63609491529302773593710803 95414237293954160390566205)
          ·
            refine ⟨35780338985232810146462327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95414237293954160390566205 35780338985232810146462327)
            ·
              refine ⟨53670508477849215219693491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35780338985232810146462327 53670508477849215219693491)
              ·
                refine ⟨80505762716773822829540237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53670508477849215219693491 80505762716773822829540237)
                ·
                  refine ⟨30189661018790183561077589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80505762716773822829540237 30189661018790183561077589)
                  ·
                    refine ⟨176892545031973731803189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30189661018790183561077589 176892545031973731803189)
                    ·
                      rfl

theorem cell23_1033491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_1033491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033491 prefixEnd_1033491 := by exact prefixLift 1033491
  have htrace : WordTrace (prefixWord ++ tailWord_1033491) baseStart_1033491 baseEnd_1033491 := by
    simpa [prefixWord, tailWord_1033491, baseEnd_1033491] using wordTrace_append hprefix tailTrace_1033491
  have hstable : (prefixWord ++ tailWord_1033491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033491).length < 2 ^ (prefixWord ++ tailWord_1033491).sum := by decide
  have hdescent : baseEnd_1033491 < baseStart_1033491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033506 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1033506 : Nat := 118140960795 + 1033506 * 2 ^ 59
def prefixEnd_1033506 : Nat := 4983230072969 + 3 ^ 40 * 1033506 * 2
def baseEnd_1033506 : Nat := 530685337305738636721999

theorem tailTrace_1033506 : CollatzResearch.WordTrace tailWord_1033506 prefixEnd_1033506 530685337305738636721999 := by
  unfold tailWord_1033506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423765148447936404332093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25130040395861163744885581 9423765148447936404332093)
  ·
    refine ⟨3533911930667976151624535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9423765148447936404332093 3533911930667976151624535)
    ·
      refine ⟨5300867896001964227436803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533911930667976151624535 5300867896001964227436803)
      ·
        refine ⟨7951301844002946341155205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300867896001964227436803 7951301844002946341155205)
        ·
          refine ⟨1490869095750552438966601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7951301844002946341155205 1490869095750552438966601)
          ·
            refine ⟨1118151821812914329224951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490869095750552438966601 1118151821812914329224951)
            ·
              refine ⟨1677227732719371493837427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118151821812914329224951 1677227732719371493837427)
              ·
                refine ⟨2515841599079057240756141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677227732719371493837427 2515841599079057240756141)
                ·
                  refine ⟨943440599654646465283553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2515841599079057240756141 943440599654646465283553)
                  ·
                    refine ⟨707580449740984848962665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943440599654646465283553 707580449740984848962665)
                    ·
                      refine ⟨530685337305738636721999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707580449740984848962665 530685337305738636721999)
                      ·
                        rfl

theorem cell23_1033506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1033506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033506 prefixEnd_1033506 := by exact prefixLift 1033506
  have htrace : WordTrace (prefixWord ++ tailWord_1033506) baseStart_1033506 baseEnd_1033506 := by
    simpa [prefixWord, tailWord_1033506, baseEnd_1033506] using wordTrace_append hprefix tailTrace_1033506
  have hstable : (prefixWord ++ tailWord_1033506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033506).length < 2 ^ (prefixWord ++ tailWord_1033506).sum := by decide
  have hdescent : baseEnd_1033506 < baseStart_1033506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033508 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1033508 : Nat := 118140960795 + 1033508 * 2 ^ 59
def prefixEnd_1033508 : Nat := 4983230072969 + 3 ^ 40 * 1033508 * 2
def baseEnd_1033508 : Nat := 176895454755682542965663

theorem tailTrace_1033508 : CollatzResearch.WordTrace tailWord_1033508 prefixEnd_1033508 176895454755682542965663 := by
  unfold tailWord_1033508
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847566769892249979450589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25130089026522999972600785 18847566769892249979450589)
  ·
    refine ⟨7067837538709593742293971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18847566769892249979450589 7067837538709593742293971)
    ·
      refine ⟨10601756308064390613440957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067837538709593742293971 10601756308064390613440957)
      ·
        refine ⟨3975658615524146480040359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10601756308064390613440957 3975658615524146480040359)
        ·
          refine ⟨5963487923286219720060539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975658615524146480040359 5963487923286219720060539)
          ·
            refine ⟨8945231884929329580090809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963487923286219720060539 8945231884929329580090809)
            ·
              refine ⟨6708923913696997185068107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945231884929329580090809 6708923913696997185068107)
              ·
                refine ⟨10063385870545495777602161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708923913696997185068107 10063385870545495777602161)
                ·
                  refine ⟨7547539402909121833201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063385870545495777602161 7547539402909121833201621)
                  ·
                    refine ⟨176895454755682542965663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7547539402909121833201621 176895454755682542965663)
                    ·
                      rfl

theorem cell23_1033508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1033508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033508 prefixEnd_1033508 := by exact prefixLift 1033508
  have htrace : WordTrace (prefixWord ++ tailWord_1033508) baseStart_1033508 baseEnd_1033508 := by
    simpa [prefixWord, tailWord_1033508, baseEnd_1033508] using wordTrace_append hprefix tailTrace_1033508
  have hstable : (prefixWord ++ tailWord_1033508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033508).length < 2 ^ (prefixWord ++ tailWord_1033508).sum := by decide
  have hdescent : baseEnd_1033508 < baseStart_1033508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033532 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_1033532 : Nat := 118140960795 + 1033532 * 2 ^ 59
def prefixEnd_1033532 : Nat := 4983230072969 + 3 ^ 40 * 1033532 * 2
def baseEnd_1033532 : Nat := 530698687802755534996879

theorem tailTrace_1033532 : CollatzResearch.WordTrace tailWord_1033532 prefixEnd_1033532 530698687802755534996879 := by
  unfold tailWord_1033532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18848004445848776028887425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25130672594465034705183233 18848004445848776028887425)
  ·
    refine ⟨14136003334386582021665569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18848004445848776028887425 14136003334386582021665569)
    ·
      refine ⟨10602002500789936516249177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14136003334386582021665569 10602002500789936516249177)
      ·
        refine ⟨7951501875592452387186883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10602002500789936516249177 7951501875592452387186883)
        ·
          refine ⟨11927252813388678580780325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951501875592452387186883 11927252813388678580780325)
          ·
            refine ⟨2236359902510377233896311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11927252813388678580780325 2236359902510377233896311)
            ·
              refine ⟨3354539853765565850844467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236359902510377233896311 3354539853765565850844467)
              ·
                refine ⟨5031809780648348776266701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354539853765565850844467 5031809780648348776266701)
                ·
                  refine ⟨1886928667743130791100013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5031809780648348776266701 1886928667743130791100013)
                  ·
                    refine ⟨707598250403674046662505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886928667743130791100013 707598250403674046662505)
                    ·
                      refine ⟨530698687802755534996879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707598250403674046662505 530698687802755534996879)
                      ·
                        rfl

theorem cell23_1033532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_1033532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033532 prefixEnd_1033532 := by exact prefixLift 1033532
  have htrace : WordTrace (prefixWord ++ tailWord_1033532) baseStart_1033532 baseEnd_1033532 := by
    simpa [prefixWord, tailWord_1033532, baseEnd_1033532] using wordTrace_append hprefix tailTrace_1033532
  have hstable : (prefixWord ++ tailWord_1033532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033532).length < 2 ^ (prefixWord ++ tailWord_1033532).sum := by decide
  have hdescent : baseEnd_1033532 < baseStart_1033532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033545 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 4, 2]
def baseStart_1033545 : Nat := 118140960795 + 1033545 * 2 ^ 59
def prefixEnd_1033545 : Nat := 4983230072969 + 3 ^ 40 * 1033545 * 2
def baseEnd_1033545 : Nat := 530705363051263984134319

theorem tailTrace_1033545 : CollatzResearch.WordTrace tailWord_1033545 prefixEnd_1033545 530705363051263984134319 := by
  unfold tailWord_1033545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37696483040650455277998089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25130988693766970185332059 37696483040650455277998089)
  ·
    refine ⟨28272362280487841458498567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37696483040650455277998089 28272362280487841458498567)
    ·
      refine ⟨42408543420731762187747851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28272362280487841458498567 42408543420731762187747851)
      ·
        refine ⟨63612815131097643281621777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42408543420731762187747851 63612815131097643281621777)
        ·
          refine ⟨47709611348323232461216333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63612815131097643281621777 47709611348323232461216333)
          ·
            refine ⟨17891104255621212172956125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47709611348323232461216333 17891104255621212172956125)
            ·
              refine ⟨6709164095857954564858547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17891104255621212172956125 6709164095857954564858547)
              ·
                refine ⟨10063746143786931847287821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709164095857954564858547 10063746143786931847287821)
                ·
                  refine ⟨3773904803920099442732933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10063746143786931847287821 3773904803920099442732933)
                  ·
                    refine ⟨707607150735018645512425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773904803920099442732933 707607150735018645512425)
                    ·
                      refine ⟨530705363051263984134319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707607150735018645512425 530705363051263984134319)
                      ·
                        rfl

theorem cell23_1033545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4, 2].length) (baseStart_1033545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033545 prefixEnd_1033545 := by exact prefixLift 1033545
  have htrace : WordTrace (prefixWord ++ tailWord_1033545) baseStart_1033545 baseEnd_1033545 := by
    simpa [prefixWord, tailWord_1033545, baseEnd_1033545] using wordTrace_append hprefix tailTrace_1033545
  have hstable : (prefixWord ++ tailWord_1033545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033545).length < 2 ^ (prefixWord ++ tailWord_1033545).sum := by decide
  have hdescent : baseEnd_1033545 < baseStart_1033545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033562 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_1033562 : Nat := 118140960795 + 1033562 * 2 ^ 59
def prefixEnd_1033562 : Nat := 4983230072969 + 3 ^ 40 * 1033562 * 2
def baseEnd_1033562 : Nat := 530714092222390417621741

theorem tailTrace_1033562 : CollatzResearch.WordTrace tailWord_1033562 prefixEnd_1033562 530714092222390417621741 := by
  unfold tailWord_1033562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424275770397216795341735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25131402054392578120911293 9424275770397216795341735)
  ·
    refine ⟨14136413655595825193012603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9424275770397216795341735 14136413655595825193012603)
    ·
      refine ⟨21204620483393737789518905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14136413655595825193012603 21204620483393737789518905)
      ·
        refine ⟨15903465362545303342139179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21204620483393737789518905 15903465362545303342139179)
        ·
          refine ⟨23855198043817955013208769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903465362545303342139179 23855198043817955013208769)
          ·
            refine ⟨17891398532863466259906577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23855198043817955013208769 17891398532863466259906577)
            ·
              refine ⟨13418548899647599694929933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891398532863466259906577 13418548899647599694929933)
              ·
                refine ⟨5031955837367849885598725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418548899647599694929933 5031955837367849885598725)
                ·
                  refine ⟨943491719506471853549761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5031955837367849885598725 943491719506471853549761)
                  ·
                    refine ⟨707618789629853890162321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943491719506471853549761 707618789629853890162321)
                    ·
                      refine ⟨530714092222390417621741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707618789629853890162321 530714092222390417621741)
                      ·
                        rfl

theorem cell23_1033562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_1033562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033562 prefixEnd_1033562 := by exact prefixLift 1033562
  have htrace : WordTrace (prefixWord ++ tailWord_1033562) baseStart_1033562 baseEnd_1033562 := by
    simpa [prefixWord, tailWord_1033562, baseEnd_1033562] using wordTrace_append hprefix tailTrace_1033562
  have hstable : (prefixWord ++ tailWord_1033562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033562).length < 2 ^ (prefixWord ++ tailWord_1033562).sum := by decide
  have hdescent : baseEnd_1033562 < baseStart_1033562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033630 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1033630 : Nat := 118140960795 + 1033630 * 2 ^ 59
def prefixEnd_1033630 : Nat := 4983230072969 + 3 ^ 40 * 1033630 * 2
def baseEnd_1033630 : Nat := 530749008906896151571429

theorem tailTrace_1033630 : CollatzResearch.WordTrace tailWord_1033630 prefixEnd_1033630 530749008906896151571429 := by
  unfold tailWord_1033630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712447905667814349355293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25133055496895009863228229 4712447905667814349355293)
  ·
    refine ⟨1767167964625430381008235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4712447905667814349355293 1767167964625430381008235)
    ·
      refine ⟨2650751946938145571512353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767167964625430381008235 2650751946938145571512353)
      ·
        refine ⟨1988063960203609178634265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650751946938145571512353 1988063960203609178634265)
        ·
          refine ⟨1491047970152706883975699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988063960203609178634265 1491047970152706883975699)
          ·
            refine ⟨2236571955229060325963549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491047970152706883975699 2236571955229060325963549)
            ·
              refine ⟨838714483210897622236331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2236571955229060325963549 838714483210897622236331)
              ·
                refine ⟨1258071724816346433354497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838714483210897622236331 1258071724816346433354497)
                ·
                  refine ⟨943553793612259825015873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258071724816346433354497 943553793612259825015873)
                  ·
                    refine ⟨707665345209194868761905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943553793612259825015873 707665345209194868761905)
                    ·
                      refine ⟨530749008906896151571429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707665345209194868761905 530749008906896151571429)
                      ·
                        rfl

theorem cell23_1033630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1033630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033630 prefixEnd_1033630 := by exact prefixLift 1033630
  have htrace : WordTrace (prefixWord ++ tailWord_1033630) baseStart_1033630 baseEnd_1033630 := by
    simpa [prefixWord, tailWord_1033630, baseEnd_1033630] using wordTrace_append hprefix tailTrace_1033630
  have hstable : (prefixWord ++ tailWord_1033630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033630).length < 2 ^ (prefixWord ++ tailWord_1033630).sum := by decide
  have hdescent : baseEnd_1033630 < baseStart_1033630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033648 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1033648 : Nat := 118140960795 + 1033648 * 2 ^ 59
def prefixEnd_1033648 : Nat := 4983230072969 + 3 ^ 40 * 1033648 * 2
def baseEnd_1033648 : Nat := 530758251558677081146345

theorem tailTrace_1033648 : CollatzResearch.WordTrace tailWord_1033648 prefixEnd_1033648 530758251558677081146345 := by
  unfold tailWord_1033648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850119879638651934498799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25133493172851535912665065 18850119879638651934498799)
  ·
    refine ⟨28275179819457977901748199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18850119879638651934498799 28275179819457977901748199)
    ·
      refine ⟨42412769729186966852622299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28275179819457977901748199 42412769729186966852622299)
      ·
        refine ⟨63619154593780450278933449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42412769729186966852622299 63619154593780450278933449)
        ·
          refine ⟨47714365945335337709200087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63619154593780450278933449 47714365945335337709200087)
          ·
            refine ⟨71571548918003006563800131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47714365945335337709200087 71571548918003006563800131)
            ·
              refine ⟨107357323377004509845700197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71571548918003006563800131 107357323377004509845700197)
              ·
                refine ⟨20129498133188345596068787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107357323377004509845700197 20129498133188345596068787)
                ·
                  refine ⟨30194247199782518394103181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20129498133188345596068787 30194247199782518394103181)
                  ·
                    refine ⟨11322842699918444397788693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30194247199782518394103181 11322842699918444397788693)
                    ·
                      refine ⟨530758251558677081146345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11322842699918444397788693 530758251558677081146345)
                      ·
                        rfl

theorem cell23_1033648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1033648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033648 prefixEnd_1033648 := by exact prefixLift 1033648
  have htrace : WordTrace (prefixWord ++ tailWord_1033648) baseStart_1033648 baseEnd_1033648 := by
    simpa [prefixWord, tailWord_1033648, baseEnd_1033648] using wordTrace_append hprefix tailTrace_1033648
  have hstable : (prefixWord ++ tailWord_1033648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033648).length < 2 ^ (prefixWord ++ tailWord_1033648).sum := by decide
  have hdescent : baseEnd_1033648 < baseStart_1033648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033655 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1033655 : Nat := 118140960795 + 1033655 * 2 ^ 59
def prefixEnd_1033655 : Nat := 4983230072969 + 3 ^ 40 * 1033655 * 2
def baseEnd_1033655 : Nat := 530761845923258553758813

theorem tailTrace_1033655 : CollatzResearch.WordTrace tailWord_1033655 prefixEnd_1033655 530761845923258553758813 := by
  unfold tailWord_1033655
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700495070251944064502419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25133663380167962709668279 37700495070251944064502419)
  ·
    refine ⟨56550742605377916096753629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37700495070251944064502419 56550742605377916096753629)
    ·
      refine ⟨21206528477016718536282611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56550742605377916096753629 21206528477016718536282611)
      ·
        refine ⟨31809792715525077804423917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206528477016718536282611 31809792715525077804423917)
        ·
          refine ⟨11928672268321904176658969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31809792715525077804423917 11928672268321904176658969)
          ·
            refine ⟨8946504201241428132494227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928672268321904176658969 8946504201241428132494227)
            ·
              refine ⟨13419756301862142198741341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946504201241428132494227 13419756301862142198741341)
              ·
                refine ⟨5032408613198303324528003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13419756301862142198741341 5032408613198303324528003)
                ·
                  refine ⟨7548612919797454986792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032408613198303324528003 7548612919797454986792005)
                  ·
                    refine ⟨1415364922462022810023501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548612919797454986792005 1415364922462022810023501)
                    ·
                      refine ⟨530761845923258553758813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415364922462022810023501 530761845923258553758813)
                      ·
                        rfl

theorem cell23_1033655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1033655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033655 prefixEnd_1033655 := by exact prefixLift 1033655
  have htrace : WordTrace (prefixWord ++ tailWord_1033655) baseStart_1033655 baseEnd_1033655 := by
    simpa [prefixWord, tailWord_1033655, baseEnd_1033655] using wordTrace_append hprefix tailTrace_1033655
  have hstable : (prefixWord ++ tailWord_1033655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033655).length < 2 ^ (prefixWord ++ tailWord_1033655).sum := by decide
  have hdescent : baseEnd_1033655 < baseStart_1033655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033672 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1033672 : Nat := 118140960795 + 1033672 * 2 ^ 59
def prefixEnd_1033672 : Nat := 4983230072969 + 3 ^ 40 * 1033672 * 2
def baseEnd_1033672 : Nat := 530770575094384987246235

theorem tailTrace_1033672 : CollatzResearch.WordTrace tailWord_1033672 prefixEnd_1033672 530770575094384987246235 := by
  unfold tailWord_1033672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850557555595177983935635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25134076740793570645247513 18850557555595177983935635)
  ·
    refine ⟨28275836333392766975903453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18850557555595177983935635 28275836333392766975903453)
    ·
      refine ⟨10603438625022287615963795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28275836333392766975903453 10603438625022287615963795)
      ·
        refine ⟨15905157937533431423945693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10603438625022287615963795 15905157937533431423945693)
        ·
          refine ⟨5964434226575036783979635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15905157937533431423945693 5964434226575036783979635)
          ·
            refine ⟨8946651339862555175969453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964434226575036783979635 8946651339862555175969453)
            ·
              refine ⟨3354994252448458190988545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8946651339862555175969453 3354994252448458190988545)
              ·
                refine ⟨2516245689336343643241409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354994252448458190988545 2516245689336343643241409)
                ·
                  refine ⟨1887184267002257732431057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516245689336343643241409 1887184267002257732431057)
                  ·
                    refine ⟨1415388200251693299323293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1887184267002257732431057 1415388200251693299323293)
                    ·
                      refine ⟨530770575094384987246235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415388200251693299323293 530770575094384987246235)
                      ·
                        rfl

theorem cell23_1033672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1033672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033672 prefixEnd_1033672 := by exact prefixLift 1033672
  have htrace : WordTrace (prefixWord ++ tailWord_1033672) baseStart_1033672 baseEnd_1033672 := by
    simpa [prefixWord, tailWord_1033672, baseEnd_1033672] using wordTrace_append hprefix tailTrace_1033672
  have hstable : (prefixWord ++ tailWord_1033672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033672).length < 2 ^ (prefixWord ++ tailWord_1033672).sum := by decide
  have hdescent : baseEnd_1033672 < baseStart_1033672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033726 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1033726 : Nat := 118140960795 + 1033726 * 2 ^ 59
def prefixEnd_1033726 : Nat := 4983230072969 + 3 ^ 40 * 1033726 * 2
def baseEnd_1033726 : Nat := 58977589227747530663443

theorem tailTrace_1033726 : CollatzResearch.WordTrace tailWord_1033726 prefixEnd_1033726 58977589227747530663443 := by
  unfold tailWord_1033726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712885581624340398792129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25135389768663148793558021 4712885581624340398792129)
  ·
    refine ⟨3534664186218255299094097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4712885581624340398792129 3534664186218255299094097)
    ·
      refine ⟨2650998139663691474320573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534664186218255299094097 2650998139663691474320573)
      ·
        refine ⟨994124302373884302870215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2650998139663691474320573 994124302373884302870215)
        ·
          refine ⟨1491186453560826454305323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994124302373884302870215 1491186453560826454305323)
          ·
            refine ⟨2236779680341239681457985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491186453560826454305323 2236779680341239681457985)
            ·
              refine ⟨1677584760255929761093489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236779680341239681457985 1677584760255929761093489)
              ·
                refine ⟨1258188570191947320820117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677584760255929761093489 1258188570191947320820117)
                ·
                  refine ⟨58977589227747530663443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1258188570191947320820117 58977589227747530663443)
                  ·
                    rfl

theorem cell23_1033726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1033726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033726 prefixEnd_1033726 := by exact prefixLift 1033726
  have htrace : WordTrace (prefixWord ++ tailWord_1033726) baseStart_1033726 baseEnd_1033726 := by
    simpa [prefixWord, tailWord_1033726, baseEnd_1033726] using wordTrace_append hprefix tailTrace_1033726
  have hstable : (prefixWord ++ tailWord_1033726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033726).length < 2 ^ (prefixWord ++ tailWord_1033726).sum := by decide
  have hdescent : baseEnd_1033726 < baseStart_1033726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033730 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1033730 : Nat := 118140960795 + 1033730 * 2 ^ 59
def prefixEnd_1033730 : Nat := 4983230072969 + 3 ^ 40 * 1033730 * 2
def baseEnd_1033730 : Nat := 176933452324115253440323

theorem tailTrace_1033730 : CollatzResearch.WordTrace tailWord_1033730 prefixEnd_1033730 176933452324115253440323 := by
  unfold tailWord_1033730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425807636245057968370661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25135487029986821248988429 9425807636245057968370661)
  ·
    refine ⟨1767338931795948369069499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9425807636245057968370661 1767338931795948369069499)
    ·
      refine ⟨2651008397693922553604249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767338931795948369069499 2651008397693922553604249)
      ·
        refine ⟨1988256298270441915203187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651008397693922553604249 1988256298270441915203187)
        ·
          refine ⟨2982384447405662872804781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988256298270441915203187 2982384447405662872804781)
          ·
            refine ⟨1118394167777123577301793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2982384447405662872804781 1118394167777123577301793)
            ·
              refine ⟨838795625832842682976345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118394167777123577301793 838795625832842682976345)
              ·
                refine ⟨629096719374632012232259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838795625832842682976345 629096719374632012232259)
                ·
                  refine ⟨943645079061948018348389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629096719374632012232259 943645079061948018348389)
                  ·
                    refine ⟨176933452324115253440323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943645079061948018348389 176933452324115253440323)
                    ·
                      rfl

theorem cell23_1033730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1033730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033730 prefixEnd_1033730 := by exact prefixLift 1033730
  have htrace : WordTrace (prefixWord ++ tailWord_1033730) baseStart_1033730 baseEnd_1033730 := by
    simpa [prefixWord, tailWord_1033730, baseEnd_1033730] using wordTrace_append hprefix tailTrace_1033730
  have hstable : (prefixWord ++ tailWord_1033730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033730).length < 2 ^ (prefixWord ++ tailWord_1033730).sum := by decide
  have hdescent : baseEnd_1033730 < baseStart_1033730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033745 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_1033745 : Nat := 118140960795 + 1033745 * 2 ^ 59
def prefixEnd_1033745 : Nat := 4983230072969 + 3 ^ 40 * 1033745 * 2
def baseEnd_1033745 : Nat := 530808059182163201633399

theorem tailTrace_1033745 : CollatzResearch.WordTrace tailWord_1033745 prefixEnd_1033745 530808059182163201633399 := by
  unfold tailWord_1033745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37703777639925889435278689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25135851759950592956852459 37703777639925889435278689)
  ·
    refine ⟨28277833229944417076459017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37703777639925889435278689 28277833229944417076459017)
    ·
      refine ⟨21208374922458312807344263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28277833229944417076459017 21208374922458312807344263)
      ·
        refine ⟨31812562383687469211016395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21208374922458312807344263 31812562383687469211016395)
        ·
          refine ⟨47718843575531203816524593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31812562383687469211016395 47718843575531203816524593)
          ·
            refine ⟨35789132681648402862393445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47718843575531203816524593 35789132681648402862393445)
            ·
              refine ⟨6710462377809075536698771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35789132681648402862393445 6710462377809075536698771)
              ·
                refine ⟨10065693566713613305048157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710462377809075536698771 10065693566713613305048157)
                ·
                  refine ⟨3774635087517604989393059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10065693566713613305048157 3774635087517604989393059)
                  ·
                    refine ⟨5661952631276407484089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774635087517604989393059 5661952631276407484089589)
                    ·
                      refine ⟨530808059182163201633399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5661952631276407484089589 530808059182163201633399)
                      ·
                        rfl

theorem cell23_1033745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_1033745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033745 prefixEnd_1033745 := by exact prefixLift 1033745
  have htrace : WordTrace (prefixWord ++ tailWord_1033745) baseStart_1033745 baseEnd_1033745 := by
    simpa [prefixWord, tailWord_1033745, baseEnd_1033745] using wordTrace_append hprefix tailTrace_1033745
  have hstable : (prefixWord ++ tailWord_1033745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033745).length < 2 ^ (prefixWord ++ tailWord_1033745).sum := by decide
  have hdescent : baseEnd_1033745 < baseStart_1033745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033759 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 5, 2, 2]
def baseStart_1033759 : Nat := 118140960795 + 1033759 * 2 ^ 59
def prefixEnd_1033759 : Nat := 4983230072969 + 3 ^ 40 * 1033759 * 2
def baseEnd_1033759 : Nat := 530815247911326146858335

theorem tailTrace_1033759 : CollatzResearch.WordTrace tailWord_1033759 prefixEnd_1033759 530815247911326146858335 := by
  unfold tailWord_1033759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704288261875169826288331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25136192174583446550858887 37704288261875169826288331)
  ·
    refine ⟨56556432392812754739432497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37704288261875169826288331 56556432392812754739432497)
    ·
      refine ⟨42417324294609566054574373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56556432392812754739432497 42417324294609566054574373)
      ·
        refine ⟨7953248305239293635232695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42417324294609566054574373 7953248305239293635232695)
        ·
          refine ⟨11929872457858940452849043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953248305239293635232695 11929872457858940452849043)
          ·
            refine ⟨17894808686788410679273565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11929872457858940452849043 17894808686788410679273565)
            ·
              refine ⟨6710553257545654004727587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17894808686788410679273565 6710553257545654004727587)
              ·
                refine ⟨10065829886318481007091381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710553257545654004727587 10065829886318481007091381)
                ·
                  refine ⟨943671551842357594414817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10065829886318481007091381 943671551842357594414817)
                  ·
                    refine ⟨707753663881768195811113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943671551842357594414817 707753663881768195811113)
                    ·
                      refine ⟨530815247911326146858335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707753663881768195811113 530815247911326146858335)
                      ·
                        rfl

theorem cell23_1033759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_1033759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033759 prefixEnd_1033759 := by exact prefixLift 1033759
  have htrace : WordTrace (prefixWord ++ tailWord_1033759) baseStart_1033759 baseEnd_1033759 := by
    simpa [prefixWord, tailWord_1033759, baseEnd_1033759] using wordTrace_append hprefix tailTrace_1033759
  have hstable : (prefixWord ++ tailWord_1033759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033759).length < 2 ^ (prefixWord ++ tailWord_1033759).sum := by decide
  have hdescent : baseEnd_1033759 < baseStart_1033759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033763 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 2, 3, 2]
def baseStart_1033763 : Nat := 118140960795 + 1033763 * 2 ^ 59
def prefixEnd_1033763 : Nat := 4983230072969 + 3 ^ 40 * 1033763 * 2
def baseEnd_1033763 : Nat := 530817301833944131208317

theorem tailTrace_1033763 : CollatzResearch.WordTrace tailWord_1033763 prefixEnd_1033763 530817301833944131208317 := by
  unfold tailWord_1033763
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704434153860678509433943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25136289435907119006289295 37704434153860678509433943)
  ·
    refine ⟨56556651230791017764150915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37704434153860678509433943 56556651230791017764150915)
    ·
      refine ⟨84834976846186526646226373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56556651230791017764150915 84834976846186526646226373)
      ·
        refine ⟨15906558158659973746167445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84834976846186526646226373 15906558158659973746167445)
        ·
          refine ⟨745619913687186269351599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15906558158659973746167445 745619913687186269351599)
          ·
            refine ⟨1118429870530779404027399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745619913687186269351599 1118429870530779404027399)
            ·
              refine ⟨1677644805796169106041099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118429870530779404027399 1677644805796169106041099)
              ·
                refine ⟨2516467208694253659061649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677644805796169106041099 2516467208694253659061649)
                ·
                  refine ⟨1887350406520690244296237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516467208694253659061649 1887350406520690244296237)
                  ·
                    refine ⟨707756402445258841611089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887350406520690244296237 707756402445258841611089)
                    ·
                      refine ⟨530817301833944131208317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707756402445258841611089 530817301833944131208317)
                      ·
                        rfl

theorem cell23_1033763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_1033763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033763 prefixEnd_1033763 := by exact prefixLift 1033763
  have htrace : WordTrace (prefixWord ++ tailWord_1033763) baseStart_1033763 baseEnd_1033763 := by
    simpa [prefixWord, tailWord_1033763, baseEnd_1033763] using wordTrace_append hprefix tailTrace_1033763
  have hstable : (prefixWord ++ tailWord_1033763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033763).length < 2 ^ (prefixWord ++ tailWord_1033763).sum := by decide
  have hdescent : baseEnd_1033763 < baseStart_1033763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033779 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 3]
def baseStart_1033779 : Nat := 118140960795 + 1033779 * 2 ^ 59
def prefixEnd_1033779 : Nat := 4983230072969 + 3 ^ 40 * 1033779 * 2
def baseEnd_1033779 : Nat := 530825517524416068608243

theorem tailTrace_1033779 : CollatzResearch.WordTrace tailWord_1033779 prefixEnd_1033779 530825517524416068608243 := by
  unfold tailWord_1033779
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705017721802713242016391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25136678481201808828010927 37705017721802713242016391)
  ·
    refine ⟨56557526582704069863024587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37705017721802713242016391 56557526582704069863024587)
    ·
      refine ⟨84836289874056104794536881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56557526582704069863024587 84836289874056104794536881)
      ·
        refine ⟨63627217405542078595902661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84836289874056104794536881 63627217405542078595902661)
        ·
          refine ⟨11930103263539139736731749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63627217405542078595902661 11930103263539139736731749)
          ·
            refine ⟨2236894361913588700637203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11930103263539139736731749 2236894361913588700637203)
            ·
              refine ⟨3355341542870383050955805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236894361913588700637203 3355341542870383050955805)
              ·
                refine ⟨1258253078576393644108427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3355341542870383050955805 1258253078576393644108427)
                ·
                  refine ⟨1887379617864590466162641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258253078576393644108427 1887379617864590466162641)
                  ·
                    refine ⟨1415534713398442849621981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1887379617864590466162641 1415534713398442849621981)
                    ·
                      refine ⟨530825517524416068608243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415534713398442849621981 530825517524416068608243)
                      ·
                        rfl

theorem cell23_1033779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_1033779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033779 prefixEnd_1033779 := by exact prefixLift 1033779
  have htrace : WordTrace (prefixWord ++ tailWord_1033779) baseStart_1033779 baseEnd_1033779 := by
    simpa [prefixWord, tailWord_1033779, baseEnd_1033779] using wordTrace_append hprefix tailTrace_1033779
  have hstable : (prefixWord ++ tailWord_1033779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033779).length < 2 ^ (prefixWord ++ tailWord_1033779).sum := by decide
  have hdescent : baseEnd_1033779 < baseStart_1033779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033793 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1033793 : Nat := 118140960795 + 1033793 * 2 ^ 59
def prefixEnd_1033793 : Nat := 4983230072969 + 3 ^ 40 * 1033793 * 2
def baseEnd_1033793 : Nat := 530832706253579013833179

theorem tailTrace_1033793 : CollatzResearch.WordTrace tailWord_1033793 prefixEnd_1033793 530832706253579013833179 := by
  unfold tailWord_1033793
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705528343751993633026033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25137018895834662422017355 37705528343751993633026033)
  ·
    refine ⟨28279146257813995224769525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37705528343751993633026033 28279146257813995224769525)
    ·
      refine ⟨2651169961670062052322143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28279146257813995224769525 2651169961670062052322143)
      ·
        refine ⟨3976754942505093078483215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651169961670062052322143 3976754942505093078483215)
        ·
          refine ⟨5965132413757639617724823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976754942505093078483215 5965132413757639617724823)
          ·
            refine ⟨8947698620636459426587235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965132413757639617724823 8947698620636459426587235)
            ·
              refine ⟨13421547930954689139880853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947698620636459426587235 13421547930954689139880853)
              ·
                refine ⟨629135059263501053431915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13421547930954689139880853 629135059263501053431915)
                ·
                  refine ⟨943702588895251580147873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629135059263501053431915 943702588895251580147873)
                  ·
                    refine ⟨707776941671438685110905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943702588895251580147873 707776941671438685110905)
                    ·
                      refine ⟨530832706253579013833179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 707776941671438685110905 530832706253579013833179)
                      ·
                        rfl

theorem cell23_1033793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1033793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033793 prefixEnd_1033793 := by exact prefixLift 1033793
  have htrace : WordTrace (prefixWord ++ tailWord_1033793) baseStart_1033793 baseEnd_1033793 := by
    simpa [prefixWord, tailWord_1033793, baseEnd_1033793] using wordTrace_append hprefix tailTrace_1033793
  have hstable : (prefixWord ++ tailWord_1033793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033793).length < 2 ^ (prefixWord ++ tailWord_1033793).sum := by decide
  have hdescent : baseEnd_1033793 < baseStart_1033793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033852 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_1033852 : Nat := 118140960795 + 1033852 * 2 ^ 59
def prefixEnd_1033852 : Nat := 4983230072969 + 3 ^ 40 * 1033852 * 2
def baseEnd_1033852 : Nat := 530863001612194282995407

theorem tailTrace_1033852 : CollatzResearch.WordTrace tailWord_1033852 prefixEnd_1033852 530863001612194282995407 := by
  unfold tailWord_1033852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853840125269123354711905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25138453500358831139615873 18853840125269123354711905)
  ·
    refine ⟨14140380093951842516033929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18853840125269123354711905 14140380093951842516033929)
    ·
      refine ⟨10605285070463881887025447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14140380093951842516033929 10605285070463881887025447)
      ·
        refine ⟨15907927605695822830538171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605285070463881887025447 15907927605695822830538171)
        ·
          refine ⟨23861891408543734245807257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907927605695822830538171 23861891408543734245807257)
          ·
            refine ⟨17896418556407800684355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23861891408543734245807257 17896418556407800684355443)
            ·
              refine ⟨26844627834611701026533165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17896418556407800684355443 26844627834611701026533165)
              ·
                refine ⟨10066735437979387884949937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26844627834611701026533165 10066735437979387884949937)
                ·
                  refine ⟨7550051578484540913712453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066735437979387884949937 7550051578484540913712453)
                  ·
                    refine ⟨1415634670965851421321085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550051578484540913712453 1415634670965851421321085)
                    ·
                      refine ⟨530863001612194282995407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415634670965851421321085 530863001612194282995407)
                      ·
                        rfl

theorem cell23_1033852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_1033852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033852 prefixEnd_1033852 := by exact prefixLift 1033852
  have htrace : WordTrace (prefixWord ++ tailWord_1033852) baseStart_1033852 baseEnd_1033852 := by
    simpa [prefixWord, tailWord_1033852, baseEnd_1033852] using wordTrace_append hprefix tailTrace_1033852
  have hstable : (prefixWord ++ tailWord_1033852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033852).length < 2 ^ (prefixWord ++ tailWord_1033852).sum := by decide
  have hdescent : baseEnd_1033852 < baseStart_1033852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033860 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_1033860 : Nat := 118140960795 + 1033860 * 2 ^ 59
def prefixEnd_1033860 : Nat := 4983230072969 + 3 ^ 40 * 1033860 * 2
def baseEnd_1033860 : Nat := 530867109457430251695371

theorem tailTrace_1033860 : CollatzResearch.WordTrace tailWord_1033860 prefixEnd_1033860 530867109457430251695371 := by
  unfold tailWord_1033860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853986017254632037857517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25138648023006176050476689 18853986017254632037857517)
  ·
    refine ⟨7070244756470487014196569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18853986017254632037857517 7070244756470487014196569)
    ·
      refine ⟨5302683567352865260647427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070244756470487014196569 5302683567352865260647427)
      ·
        refine ⟨7954025351029297890971141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302683567352865260647427 7954025351029297890971141)
        ·
          refine ⟨1491379753317993354557089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7954025351029297890971141 1491379753317993354557089)
          ·
            refine ⟨1118534814988495015917817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491379753317993354557089 1118534814988495015917817)
            ·
              refine ⟨838901111241371261938363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118534814988495015917817 838901111241371261938363)
              ·
                refine ⟨1258351666862056892907545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838901111241371261938363 1258351666862056892907545)
                ·
                  refine ⟨943763750146542669680659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258351666862056892907545 943763750146542669680659)
                  ·
                    refine ⟨1415645625219814004520989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943763750146542669680659 1415645625219814004520989)
                    ·
                      refine ⟨530867109457430251695371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415645625219814004520989 530867109457430251695371)
                      ·
                        rfl

theorem cell23_1033860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_1033860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033860 prefixEnd_1033860 := by exact prefixLift 1033860
  have htrace : WordTrace (prefixWord ++ tailWord_1033860) baseStart_1033860 baseEnd_1033860 := by
    simpa [prefixWord, tailWord_1033860, baseEnd_1033860] using wordTrace_append hprefix tailTrace_1033860
  have hstable : (prefixWord ++ tailWord_1033860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033860).length < 2 ^ (prefixWord ++ tailWord_1033860).sum := by decide
  have hdescent : baseEnd_1033860 < baseStart_1033860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033906 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_1033906 : Nat := 118140960795 + 1033906 * 2 ^ 59
def prefixEnd_1033906 : Nat := 4983230072969 + 3 ^ 40 * 1033906 * 2
def baseEnd_1033906 : Nat := 58987858840837452413351

theorem tailTrace_1033906 : CollatzResearch.WordTrace tailWord_1033906 prefixEnd_1033906 58987858840837452413351 := by
  unfold tailWord_1033906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427412448085653482972393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25139766528228409287926381 9427412448085653482972393)
  ·
    refine ⟨7070559336064240112229295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9427412448085653482972393 7070559336064240112229295)
    ·
      refine ⟨10605839004096360168343943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070559336064240112229295 10605839004096360168343943)
      ·
        refine ⟨15908758506144540252515915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605839004096360168343943 15908758506144540252515915)
        ·
          refine ⟨23863137759216810378773873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908758506144540252515915 23863137759216810378773873)
          ·
            refine ⟨17897353319412607784080405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23863137759216810378773873 17897353319412607784080405)
            ·
              refine ⟨838938436847465989878769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17897353319412607784080405 838938436847465989878769)
              ·
                refine ⟨629203827635599492409077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838938436847465989878769 629203827635599492409077)
                ·
                  refine ⟨58987858840837452413351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629203827635599492409077 58987858840837452413351)
                  ·
                    rfl

theorem cell23_1033906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_1033906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033906 prefixEnd_1033906 := by exact prefixLift 1033906
  have htrace : WordTrace (prefixWord ++ tailWord_1033906) baseStart_1033906 baseEnd_1033906 := by
    simpa [prefixWord, tailWord_1033906, baseEnd_1033906] using wordTrace_append hprefix tailTrace_1033906
  have hstable : (prefixWord ++ tailWord_1033906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033906).length < 2 ^ (prefixWord ++ tailWord_1033906).sum := by decide
  have hdescent : baseEnd_1033906 < baseStart_1033906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033952 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1033952 : Nat := 118140960795 + 1033952 * 2 ^ 59
def prefixEnd_1033952 : Nat := 4983230072969 + 3 ^ 40 * 1033952 * 2
def baseEnd_1033952 : Nat := 530914349677643891744947

theorem tailTrace_1033952 : CollatzResearch.WordTrace tailWord_1033952 prefixEnd_1033952 530914349677643891744947 := by
  unfold tailWord_1033952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855663775087981894032055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25140885033450642525376073 18855663775087981894032055)
  ·
    refine ⟨28283495662631972841048083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855663775087981894032055 28283495662631972841048083)
    ·
      refine ⟨42425243493947959261572125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28283495662631972841048083 42425243493947959261572125)
      ·
        refine ⟨15909466310230484723089547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42425243493947959261572125 15909466310230484723089547)
        ·
          refine ⟨23864199465345727084634321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15909466310230484723089547 23864199465345727084634321)
          ·
            refine ⟨17898149599009295313475741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23864199465345727084634321 17898149599009295313475741)
            ·
              refine ⟨6711806099628485742553403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17898149599009295313475741 6711806099628485742553403)
              ·
                refine ⟨10067709149442728613830105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711806099628485742553403 10067709149442728613830105)
                ·
                  refine ⟨7550781862082046460372579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10067709149442728613830105 7550781862082046460372579)
                  ·
                    refine ⟨11326172793123069690558869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550781862082046460372579 11326172793123069690558869)
                    ·
                      refine ⟨530914349677643891744947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11326172793123069690558869 530914349677643891744947)
                      ·
                        rfl

theorem cell23_1033952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1033952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033952 prefixEnd_1033952 := by exact prefixLift 1033952
  have htrace : WordTrace (prefixWord ++ tailWord_1033952) baseStart_1033952 baseEnd_1033952 := by
    simpa [prefixWord, tailWord_1033952, baseEnd_1033952] using wordTrace_append hprefix tailTrace_1033952
  have hstable : (prefixWord ++ tailWord_1033952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033952).length < 2 ^ (prefixWord ++ tailWord_1033952).sum := by decide
  have hdescent : baseEnd_1033952 < baseStart_1033952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033966 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1033966 : Nat := 118140960795 + 1033966 * 2 ^ 59
def prefixEnd_1033966 : Nat := 4983230072969 + 3 ^ 40 * 1033966 * 2
def baseEnd_1033966 : Nat := 176973846135602278989961

theorem tailTrace_1033966 : CollatzResearch.WordTrace tailWord_1033966 prefixEnd_1033966 176973846135602278989961 := by
  unfold tailWord_1033966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713979771515655522384219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25141225448083496119382501 4713979771515655522384219)
  ·
    refine ⟨7070969657273483283576329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713979771515655522384219 7070969657273483283576329)
    ·
      refine ⟨5303227242955112462682247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070969657273483283576329 5303227242955112462682247)
      ·
        refine ⟨7954840864432668694023371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303227242955112462682247 7954840864432668694023371)
        ·
          refine ⟨11932261296649003041035057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954840864432668694023371 11932261296649003041035057)
          ·
            refine ⟨8949195972486752280776293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11932261296649003041035057 8949195972486752280776293)
            ·
              refine ⟨1677974244841266052645555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8949195972486752280776293 1677974244841266052645555)
              ·
                refine ⟨2516961367261899078968333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677974244841266052645555 2516961367261899078968333)
                ·
                  refine ⟨943860512723212154613125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2516961367261899078968333 943860512723212154613125)
                  ·
                    refine ⟨176973846135602278989961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943860512723212154613125 176973846135602278989961)
                    ·
                      rfl

theorem cell23_1033966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1033966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1033966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1033966 prefixEnd_1033966 := by exact prefixLift 1033966
  have htrace : WordTrace (prefixWord ++ tailWord_1033966) baseStart_1033966 baseEnd_1033966 := by
    simpa [prefixWord, tailWord_1033966, baseEnd_1033966] using wordTrace_append hprefix tailTrace_1033966
  have hstable : (prefixWord ++ tailWord_1033966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033966).length < 2 ^ (prefixWord ++ tailWord_1033966).sum := by decide
  have hdescent : baseEnd_1033966 < baseStart_1033966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034030 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_1034030 : Nat := 118140960795 + 1034030 * 2 ^ 59
def prefixEnd_1034030 : Nat := 4983230072969 + 3 ^ 40 * 1034030 * 2
def baseEnd_1034030 : Nat := 58994933463188287396621

theorem tailTrace_1034030 : CollatzResearch.WordTrace tailWord_1034030 prefixEnd_1034030 58994933463188287396621 := by
  unfold tailWord_1034030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714271555486672888675443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25142781629262255406269029 4714271555486672888675443)
  ·
    refine ⟨7071407333230009333013165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4714271555486672888675443 7071407333230009333013165)
    ·
      refine ⟨2651777749961253499879937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7071407333230009333013165 2651777749961253499879937)
      ·
        refine ⟨1988833312470940124909953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651777749961253499879937 1988833312470940124909953)
        ·
          refine ⟨1491624984353205093682465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988833312470940124909953 1491624984353205093682465)
          ·
            refine ⟨1118718738264903820261849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491624984353205093682465 1118718738264903820261849)
            ·
              refine ⟨839039053698677865196387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118718738264903820261849 839039053698677865196387)
              ·
                refine ⟨1258558580548016797794581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839039053698677865196387 1258558580548016797794581)
                ·
                  refine ⟨58994933463188287396621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1258558580548016797794581 58994933463188287396621)
                  ·
                    rfl

theorem cell23_1034030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_1034030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034030 prefixEnd_1034030 := by exact prefixLift 1034030
  have htrace : WordTrace (prefixWord ++ tailWord_1034030) baseStart_1034030 baseEnd_1034030 := by
    simpa [prefixWord, tailWord_1034030, baseEnd_1034030] using wordTrace_append hprefix tailTrace_1034030
  have hstable : (prefixWord ++ tailWord_1034030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034030).length < 2 ^ (prefixWord ++ tailWord_1034030).sum := by decide
  have hdescent : baseEnd_1034030 < baseStart_1034030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034039 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 6, 4]
def baseStart_1034039 : Nat := 118140960795 + 1034039 * 2 ^ 59
def prefixEnd_1034039 : Nat := 4983230072969 + 3 ^ 40 * 1034039 * 2
def baseEnd_1034039 : Nat := 176986340831528350452349

theorem tailTrace_1034039 : CollatzResearch.WordTrace tailWord_1034039 prefixEnd_1034039 176986340831528350452349 := by
  unfold tailWord_1034039
  simp only [CollatzResearch.WordTrace]
  refine ⟨37714500700860777646481171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25143000467240518430987447 37714500700860777646481171)
  ·
    refine ⟨56571751051291166469721757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37714500700860777646481171 56571751051291166469721757)
    ·
      refine ⟨21214406644234187426145659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56571751051291166469721757 21214406644234187426145659)
      ·
        refine ⟨31821609966351281139218489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21214406644234187426145659 31821609966351281139218489)
        ·
          refine ⟨23866207474763460854413867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31821609966351281139218489 23866207474763460854413867)
          ·
            refine ⟨35799311212145191281620801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23866207474763460854413867 35799311212145191281620801)
            ·
              refine ⟨26849483409108893461215601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35799311212145191281620801 26849483409108893461215601)
              ·
                refine ⟨20137112556831670095911701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26849483409108893461215601 20137112556831670095911701)
                ·
                  refine ⟨943927151101484535745861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20137112556831670095911701 943927151101484535745861)
                  ·
                    refine ⟨176986340831528350452349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 943927151101484535745861 176986340831528350452349)
                    ·
                      rfl

theorem cell23_1034039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_1034039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034039 prefixEnd_1034039 := by exact prefixLift 1034039
  have htrace : WordTrace (prefixWord ++ tailWord_1034039) baseStart_1034039 baseEnd_1034039 := by
    simpa [prefixWord, tailWord_1034039, baseEnd_1034039] using wordTrace_append hprefix tailTrace_1034039
  have hstable : (prefixWord ++ tailWord_1034039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034039).length < 2 ^ (prefixWord ++ tailWord_1034039).sum := by decide
  have hdescent : baseEnd_1034039 < baseStart_1034039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034066 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1034066 : Nat := 118140960795 + 1034066 * 2 ^ 59
def prefixEnd_1034066 : Nat := 4983230072969 + 3 ^ 40 * 1034066 * 2
def baseEnd_1034066 : Nat := 530972886472256445719423

theorem tailTrace_1034066 : CollatzResearch.WordTrace tailWord_1034066 prefixEnd_1034066 530972886472256445719423 := by
  unfold tailWord_1034066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9428871367940740314428513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25143656981175307505142701 9428871367940740314428513)
  ·
    refine ⟨7071653525955555235821385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9428871367940740314428513 7071653525955555235821385)
    ·
      refine ⟨5303740144466666426866039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7071653525955555235821385 5303740144466666426866039)
      ·
        refine ⟨7955610216699999640299059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303740144466666426866039 7955610216699999640299059)
        ·
          refine ⟨11933415325049999460448589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955610216699999640299059 11933415325049999460448589)
          ·
            refine ⟨4475030746893749797668221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11933415325049999460448589 4475030746893749797668221)
            ·
              refine ⟨1678136530085156174125583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4475030746893749797668221 1678136530085156174125583)
              ·
                refine ⟨2517204795127734261188375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678136530085156174125583 2517204795127734261188375)
                ·
                  refine ⟨3775807192691601391782563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517204795127734261188375 3775807192691601391782563)
                  ·
                    refine ⟨5663710789037402087673845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775807192691601391782563 5663710789037402087673845)
                    ·
                      refine ⟨530972886472256445719423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5663710789037402087673845 530972886472256445719423)
                      ·
                        rfl

theorem cell23_1034066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1034066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034066 prefixEnd_1034066 := by exact prefixLift 1034066
  have htrace : WordTrace (prefixWord ++ tailWord_1034066) baseStart_1034066 baseEnd_1034066 := by
    simpa [prefixWord, tailWord_1034066, baseEnd_1034066] using wordTrace_append hprefix tailTrace_1034066
  have hstable : (prefixWord ++ tailWord_1034066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034066).length < 2 ^ (prefixWord ++ tailWord_1034066).sum := by decide
  have hdescent : baseEnd_1034066 < baseStart_1034066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034096 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_1034096 : Nat := 118140960795 + 1034096 * 2 ^ 59
def prefixEnd_1034096 : Nat := 4983230072969 + 3 ^ 40 * 1034096 * 2
def baseEnd_1034096 : Nat := 530988290891891328344285

theorem tailTrace_1034096 : CollatzResearch.WordTrace tailWord_1034096 prefixEnd_1034096 530988290891891328344285 := by
  unfold tailWord_1034096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858289830827138190653071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25144386441102850920870761 18858289830827138190653071)
  ·
    refine ⟨28287434746240707285979607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18858289830827138190653071 28287434746240707285979607)
    ·
      refine ⟨42431152119361060928969411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28287434746240707285979607 42431152119361060928969411)
      ·
        refine ⟨63646728179041591393454117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42431152119361060928969411 63646728179041591393454117)
        ·
          refine ⟨11933761533570298386272647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63646728179041591393454117 11933761533570298386272647)
          ·
            refine ⟨17900642300355447579408971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933761533570298386272647 17900642300355447579408971)
            ·
              refine ⟨26850963450533171369113457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900642300355447579408971 26850963450533171369113457)
              ·
                refine ⟨20138222587899878526835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26850963450533171369113457 20138222587899878526835093)
                ·
                  refine ⟨943979183807806805945395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20138222587899878526835093 943979183807806805945395)
                  ·
                    refine ⟨1415968775711710208918093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943979183807806805945395 1415968775711710208918093)
                    ·
                      refine ⟨530988290891891328344285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1415968775711710208918093 530988290891891328344285)
                      ·
                        rfl

theorem cell23_1034096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_1034096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034096 prefixEnd_1034096 := by exact prefixLift 1034096
  have htrace : WordTrace (prefixWord ++ tailWord_1034096) baseStart_1034096 baseEnd_1034096 := by
    simpa [prefixWord, tailWord_1034096, baseEnd_1034096] using wordTrace_append hprefix tailTrace_1034096
  have hstable : (prefixWord ++ tailWord_1034096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034096).length < 2 ^ (prefixWord ++ tailWord_1034096).sum := by decide
  have hdescent : baseEnd_1034096 < baseStart_1034096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034109 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1034109 : Nat := 118140960795 + 1034109 * 2 ^ 59
def prefixEnd_1034109 : Nat := 4983230072969 + 3 ^ 40 * 1034109 * 2
def baseEnd_1034109 : Nat := 530994966140399777481725

theorem tailTrace_1034109 : CollatzResearch.WordTrace tailWord_1034109 prefixEnd_1034109 530994966140399777481725 := by
  unfold tailWord_1034109
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717053810607179601529381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144702540404786401019587 37717053810607179601529381)
  ·
    refine ⟨7071947589488846175286759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37717053810607179601529381 7071947589488846175286759)
    ·
      refine ⟨10607921384233269262930139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071947589488846175286759 10607921384233269262930139)
      ·
        refine ⟨15911882076349903894395209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10607921384233269262930139 15911882076349903894395209)
        ·
          refine ⟨11933911557262427920796407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15911882076349903894395209 11933911557262427920796407)
          ·
            refine ⟨17900867335893641881194611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933911557262427920796407 17900867335893641881194611)
            ·
              refine ⟨26851301003840462821791917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900867335893641881194611 26851301003840462821791917)
              ·
                refine ⟨10069237876440173558171969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26851301003840462821791917 10069237876440173558171969)
                ·
                  refine ⟨7551928407330130168628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069237876440173558171969 7551928407330130168628977)
                  ·
                    refine ⟨5663946305497597626471733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7551928407330130168628977 5663946305497597626471733)
                    ·
                      refine ⟨530994966140399777481725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5663946305497597626471733 530994966140399777481725)
                      ·
                        rfl

theorem cell23_1034109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1034109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034109 prefixEnd_1034109 := by exact prefixLift 1034109
  have htrace : WordTrace (prefixWord ++ tailWord_1034109) baseStart_1034109 baseEnd_1034109 := by
    simpa [prefixWord, tailWord_1034109, baseEnd_1034109] using wordTrace_append hprefix tailTrace_1034109
  have hstable : (prefixWord ++ tailWord_1034109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034109).length < 2 ^ (prefixWord ++ tailWord_1034109).sum := by decide
  have hdescent : baseEnd_1034109 < baseStart_1034109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034129 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1034129 : Nat := 118140960795 + 1034129 * 2 ^ 59
def prefixEnd_1034129 : Nat := 4983230072969 + 3 ^ 40 * 1034129 * 2
def baseEnd_1034129 : Nat := 177001745251163233077211

theorem tailTrace_1034129 : CollatzResearch.WordTrace tailWord_1034129 prefixEnd_1034129 177001745251163233077211 := by
  unfold tailWord_1034129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717783270534723017257441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25145188847023148678171627 37717783270534723017257441)
  ·
    refine ⟨28288337452901042262943081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37717783270534723017257441 28288337452901042262943081)
    ·
      refine ⟨21216253089675781697207311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28288337452901042262943081 21216253089675781697207311)
      ·
        refine ⟨31824379634513672545810967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216253089675781697207311 31824379634513672545810967)
        ·
          refine ⟨47736569451770508818716451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824379634513672545810967 47736569451770508818716451)
          ·
            refine ⟨71604854177655763228074677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47736569451770508818716451 71604854177655763228074677)
            ·
              refine ⟨6712955079155227802632001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71604854177655763228074677 6712955079155227802632001)
              ·
                refine ⟨5034716309366420851974001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712955079155227802632001 5034716309366420851974001)
                ·
                  refine ⟨3776037232024815638980501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034716309366420851974001 3776037232024815638980501)
                  ·
                    refine ⟨177001745251163233077211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3776037232024815638980501 177001745251163233077211)
                    ·
                      rfl

theorem cell23_1034129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1034129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034129 prefixEnd_1034129 := by exact prefixLift 1034129
  have htrace : WordTrace (prefixWord ++ tailWord_1034129) baseStart_1034129 baseEnd_1034129 := by
    simpa [prefixWord, tailWord_1034129, baseEnd_1034129] using wordTrace_append hprefix tailTrace_1034129
  have hstable : (prefixWord ++ tailWord_1034129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034129).length < 2 ^ (prefixWord ++ tailWord_1034129).sum := by decide
  have hdescent : baseEnd_1034129 < baseStart_1034129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034130 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1034130 : Nat := 118140960795 + 1034130 * 2 ^ 59
def prefixEnd_1034130 : Nat := 4983230072969 + 3 ^ 40 * 1034130 * 2
def baseEnd_1034130 : Nat := 531005749234144195319129

theorem tailTrace_1034130 : CollatzResearch.WordTrace tailWord_1034130 prefixEnd_1034130 531005749234144195319129 := by
  unfold tailWord_1034130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429454935882775047010961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25145213162354066792029229 9429454935882775047010961)
  ·
    refine ⟨7072091201912081285258221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9429454935882775047010961 7072091201912081285258221)
    ·
      refine ⟨2652034200717030481971833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7072091201912081285258221 2652034200717030481971833)
      ·
        refine ⟨1989025650537772861478875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652034200717030481971833 1989025650537772861478875)
        ·
          refine ⟨2983538475806659292218313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989025650537772861478875 2983538475806659292218313)
          ·
            refine ⟨2237653856854994469163735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983538475806659292218313 2237653856854994469163735)
            ·
              refine ⟨3356480785282491703745603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237653856854994469163735 3356480785282491703745603)
              ·
                refine ⟨5034721177923737555618405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356480785282491703745603 5034721177923737555618405)
                ·
                  refine ⟨944010220860700791678451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5034721177923737555618405 944010220860700791678451)
                  ·
                    refine ⟨1416015331291051187517677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944010220860700791678451 1416015331291051187517677)
                    ·
                      refine ⟨531005749234144195319129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416015331291051187517677 531005749234144195319129)
                      ·
                        rfl

theorem cell23_1034130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1034130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034130 prefixEnd_1034130 := by exact prefixLift 1034130
  have htrace : WordTrace (prefixWord ++ tailWord_1034130) baseStart_1034130 baseEnd_1034130 := by
    simpa [prefixWord, tailWord_1034130, baseEnd_1034130] using wordTrace_append hprefix tailTrace_1034130
  have hstable : (prefixWord ++ tailWord_1034130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034130).length < 2 ^ (prefixWord ++ tailWord_1034130).sum := by decide
  have hdescent : baseEnd_1034130 < baseStart_1034130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034159 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 7]
def baseStart_1034159 : Nat := 118140960795 + 1034159 * 2 ^ 59
def prefixEnd_1034159 : Nat := 4983230072969 + 3 ^ 40 * 1034159 * 2
def baseEnd_1034159 : Nat := 59002293352569397984055

theorem tailTrace_1034159 : CollatzResearch.WordTrace tailWord_1034159 prefixEnd_1034159 59002293352569397984055 := by
  unfold tailWord_1034159
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718877460426038140849531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25145918306950692093899687 37718877460426038140849531)
  ·
    refine ⟨56578316190639057211274297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37718877460426038140849531 56578316190639057211274297)
    ·
      refine ⟨42433737142979292908455723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56578316190639057211274297 42433737142979292908455723)
      ·
        refine ⟨63650605714468939362683585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42433737142979292908455723 63650605714468939362683585)
        ·
          refine ⟨47737954285851704522012689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63650605714468939362683585 47737954285851704522012689)
          ·
            refine ⟨35803465714388778391509517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47737954285851704522012689 35803465714388778391509517)
            ·
              refine ⟨13426299642895791896816069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35803465714388778391509517 13426299642895791896816069)
              ·
                refine ⟨2517431183042960980653013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13426299642895791896816069 2517431183042960980653013)
                ·
                  refine ⟨59002293352569397984055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2517431183042960980653013 59002293352569397984055)
                  ·
                    rfl

theorem cell23_1034159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 7].length) (baseStart_1034159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034159 prefixEnd_1034159 := by exact prefixLift 1034159
  have htrace : WordTrace (prefixWord ++ tailWord_1034159) baseStart_1034159 baseEnd_1034159 := by
    simpa [prefixWord, tailWord_1034159, baseEnd_1034159] using wordTrace_append hprefix tailTrace_1034159
  have hstable : (prefixWord ++ tailWord_1034159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034159).length < 2 ^ (prefixWord ++ tailWord_1034159).sum := by decide
  have hdescent : baseEnd_1034159 < baseStart_1034159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034186 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1034186 : Nat := 118140960795 + 1034186 * 2 ^ 59
def prefixEnd_1034186 : Nat := 4983230072969 + 3 ^ 40 * 1034186 * 2
def baseEnd_1034186 : Nat := 531034504150795976218871

theorem tailTrace_1034186 : CollatzResearch.WordTrace tailWord_1034186 prefixEnd_1034186 531034504150795976218871 := by
  unfold tailWord_1034186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429965557832055438020603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25146574820885481168054941 9429965557832055438020603)
  ·
    refine ⟨14144948336748083157030905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9429965557832055438020603 14144948336748083157030905)
    ·
      refine ⟨10608711252561062367773179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144948336748083157030905 10608711252561062367773179)
      ·
        refine ⟨15913066878841593551659769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608711252561062367773179 15913066878841593551659769)
        ·
          refine ⟨11934800159131195163744827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15913066878841593551659769 11934800159131195163744827)
          ·
            refine ⟨17902200238696792745617241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934800159131195163744827 17902200238696792745617241)
            ·
              refine ⟨13426650179022594559212931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17902200238696792745617241 13426650179022594559212931)
              ·
                refine ⟨20139975268533891838819397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426650179022594559212931 20139975268533891838819397)
                ·
                  refine ⟨3776245362850104719778637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20139975268533891838819397 3776245362850104719778637)
                  ·
                    refine ⟨1416092011068789269916989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776245362850104719778637 1416092011068789269916989)
                    ·
                      refine ⟨531034504150795976218871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416092011068789269916989 531034504150795976218871)
                      ·
                        rfl

theorem cell23_1034186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1034186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034186 prefixEnd_1034186 := by exact prefixLift 1034186
  have htrace : WordTrace (prefixWord ++ tailWord_1034186) baseStart_1034186 baseEnd_1034186 := by
    simpa [prefixWord, tailWord_1034186, baseEnd_1034186] using wordTrace_append hprefix tailTrace_1034186
  have hstable : (prefixWord ++ tailWord_1034186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034186).length < 2 ^ (prefixWord ++ tailWord_1034186).sum := by decide
  have hdescent : baseEnd_1034186 < baseStart_1034186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034219 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 8]
def baseStart_1034219 : Nat := 118140960795 + 1034219 * 2 ^ 59
def prefixEnd_1034219 : Nat := 4983230072969 + 3 ^ 40 * 1034219 * 2
def baseEnd_1034219 : Nat := 177017149670798115702073

theorem tailTrace_1034219 : CollatzResearch.WordTrace tailWord_1034219 prefixEnd_1034219 177017149670798115702073 := by
  unfold tailWord_1034219
  simp only [CollatzResearch.WordTrace]
  refine ⟨37721065840208668388033711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25147377226805778925355807 37721065840208668388033711)
  ·
    refine ⟨56581598760313002582050567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37721065840208668388033711 56581598760313002582050567)
    ·
      refine ⟨84872398140469503873075851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56581598760313002582050567 84872398140469503873075851)
      ·
        refine ⟨127308597210704255809613777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84872398140469503873075851 127308597210704255809613777)
        ·
          refine ⟨95481447908028191857210333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127308597210704255809613777 95481447908028191857210333)
          ·
            refine ⟨35805542965510571946453875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95481447908028191857210333 35805542965510571946453875)
            ·
              refine ⟨53708314448265857919680813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35805542965510571946453875 53708314448265857919680813)
              ·
                refine ⟨20140617918099696719880305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53708314448265857919680813 20140617918099696719880305)
                ·
                  refine ⟨15105463438574772539910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20140617918099696719880305 15105463438574772539910229)
                  ·
                    refine ⟨177017149670798115702073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15105463438574772539910229 177017149670798115702073)
                    ·
                      rfl

theorem cell23_1034219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_1034219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034219 prefixEnd_1034219 := by exact prefixLift 1034219
  have htrace : WordTrace (prefixWord ++ tailWord_1034219) baseStart_1034219 baseEnd_1034219 := by
    simpa [prefixWord, tailWord_1034219, baseEnd_1034219] using wordTrace_append hprefix tailTrace_1034219
  have hstable : (prefixWord ++ tailWord_1034219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034219).length < 2 ^ (prefixWord ++ tailWord_1034219).sum := by decide
  have hdescent : baseEnd_1034219 < baseStart_1034219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034244 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1034244 : Nat := 118140960795 + 1034244 * 2 ^ 59
def prefixEnd_1034244 : Nat := 4983230072969 + 3 ^ 40 * 1034244 * 2
def baseEnd_1034244 : Nat := 59007142892084083254845

theorem tailTrace_1034244 : CollatzResearch.WordTrace tailWord_1034244 prefixEnd_1034244 59007142892084083254845 := by
  unfold tailWord_1034244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860988832559048828846893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25147985110078731771795857 18860988832559048828846893)
  ·
    refine ⟨7072870812209643310817585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18860988832559048828846893 7072870812209643310817585)
    ·
      refine ⟨5304653109157232483113189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7072870812209643310817585 5304653109157232483113189)
      ·
        refine ⟨994622457966981090583723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5304653109157232483113189 994622457966981090583723)
        ·
          refine ⟨1491933686950471635875585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994622457966981090583723 1491933686950471635875585)
          ·
            refine ⟨1118950265212853726906689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491933686950471635875585 1118950265212853726906689)
            ·
              refine ⟨839212698909640295180017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118950265212853726906689 839212698909640295180017)
              ·
                refine ⟨629409524182230221385013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839212698909640295180017 629409524182230221385013)
                ·
                  refine ⟨59007142892084083254845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629409524182230221385013 59007142892084083254845)
                  ·
                    rfl

theorem cell23_1034244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1034244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034244 prefixEnd_1034244 := by exact prefixLift 1034244
  have htrace : WordTrace (prefixWord ++ tailWord_1034244) baseStart_1034244 baseEnd_1034244 := by
    simpa [prefixWord, tailWord_1034244, baseEnd_1034244] using wordTrace_append hprefix tailTrace_1034244
  have hstable : (prefixWord ++ tailWord_1034244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034244).length < 2 ^ (prefixWord ++ tailWord_1034244).sum := by decide
  have hdescent : baseEnd_1034244 < baseStart_1034244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034343 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 6, 4]
def baseStart_1034343 : Nat := 118140960795 + 1034343 * 2 ^ 59
def prefixEnd_1034343 : Nat := 4983230072969 + 3 ^ 40 * 1034343 * 2
def baseEnd_1034343 : Nat := 177038373537850620651883

theorem tailTrace_1034343 : CollatzResearch.WordTrace tailWord_1034343 prefixEnd_1034343 177038373537850620651883 := by
  unfold tailWord_1034343
  simp only [CollatzResearch.WordTrace]
  refine ⟨37725588491759437565547683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25150392327839625043698455 37725588491759437565547683)
  ·
    refine ⟨56588382737639156348321525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37725588491759437565547683 56588382737639156348321525)
    ·
      refine ⟨5305160881653670907655143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56588382737639156348321525 5305160881653670907655143)
      ·
        refine ⟨7957741322480506361482715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305160881653670907655143 7957741322480506361482715)
        ·
          refine ⟨11936611983720759542224073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957741322480506361482715 11936611983720759542224073)
          ·
            refine ⟨8952458987790569656668055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11936611983720759542224073 8952458987790569656668055)
            ·
              refine ⟨13428688481685854485002083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8952458987790569656668055 13428688481685854485002083)
              ·
                refine ⟨20143032722528781727503125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428688481685854485002083 20143032722528781727503125)
                ·
                  refine ⟨944204658868536643476709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20143032722528781727503125 944204658868536643476709)
                  ·
                    refine ⟨177038373537850620651883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944204658868536643476709 177038373537850620651883)
                    ·
                      rfl

theorem cell23_1034343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_1034343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034343 prefixEnd_1034343 := by exact prefixLift 1034343
  have htrace : WordTrace (prefixWord ++ tailWord_1034343) baseStart_1034343 baseEnd_1034343 := by
    simpa [prefixWord, tailWord_1034343, baseEnd_1034343] using wordTrace_append hprefix tailTrace_1034343
  have hstable : (prefixWord ++ tailWord_1034343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034343).length < 2 ^ (prefixWord ++ tailWord_1034343).sum := by decide
  have hdescent : baseEnd_1034343 < baseStart_1034343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034350 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1034350 : Nat := 118140960795 + 1034350 * 2 ^ 59
def prefixEnd_1034350 : Nat := 4983230072969 + 3 ^ 40 * 1034350 * 2
def baseEnd_1034350 : Nat := 531118714978133334568117

theorem tailTrace_1034350 : CollatzResearch.WordTrace tailWord_1034350 prefixEnd_1034350 531118714978133334568117 := by
  unfold tailWord_1034350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715730475341759720131563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25150562535156051840701669 4715730475341759720131563)
  ·
    refine ⟨7073595713012639580197345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715730475341759720131563 7073595713012639580197345)
    ·
      refine ⟨5305196784759479685148009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7073595713012639580197345 5305196784759479685148009)
      ·
        refine ⟨3978897588569609763861007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5305196784759479685148009 3978897588569609763861007)
        ·
          refine ⟨5968346382854414645791511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978897588569609763861007 5968346382854414645791511)
          ·
            refine ⟨8952519574281621968687267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968346382854414645791511 8952519574281621968687267)
            ·
              refine ⟨13428779361422432953030901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8952519574281621968687267 13428779361422432953030901)
              ·
                refine ⟨1258948065133353089346647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13428779361422432953030901 1258948065133353089346647)
                ·
                  refine ⟨1888422097700029634019971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258948065133353089346647 1888422097700029634019971)
                  ·
                    refine ⟨2832633146550044451029957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1888422097700029634019971 2832633146550044451029957)
                    ·
                      refine ⟨531118714978133334568117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2832633146550044451029957 531118714978133334568117)
                      ·
                        rfl

theorem cell23_1034350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1034350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034350 prefixEnd_1034350 := by exact prefixLift 1034350
  have htrace : WordTrace (prefixWord ++ tailWord_1034350) baseStart_1034350 baseEnd_1034350 := by
    simpa [prefixWord, tailWord_1034350, baseEnd_1034350] using wordTrace_append hprefix tailTrace_1034350
  have hstable : (prefixWord ++ tailWord_1034350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034350).length < 2 ^ (prefixWord ++ tailWord_1034350).sum := by decide
  have hdescent : baseEnd_1034350 < baseStart_1034350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034353 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_1034353 : Nat := 118140960795 + 1034353 * 2 ^ 59
def prefixEnd_1034353 : Nat := 4983230072969 + 3 ^ 40 * 1034353 * 2
def baseEnd_1034353 : Nat := 531120255420096822830603

theorem tailTrace_1034353 : CollatzResearch.WordTrace tailWord_1034353 prefixEnd_1034353 531120255420096822830603 := by
  unfold tailWord_1034353
  simp only [CollatzResearch.WordTrace]
  refine ⟨37725953221723209273411713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25150635481148806182274475 37725953221723209273411713)
  ·
    refine ⟨28294464916292406955058785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37725953221723209273411713 28294464916292406955058785)
    ·
      refine ⟨21220848687219305216294089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28294464916292406955058785 21220848687219305216294089)
      ·
        refine ⟨15915636515414478912220567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21220848687219305216294089 15915636515414478912220567)
        ·
          refine ⟨23873454773121718368330851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15915636515414478912220567 23873454773121718368330851)
          ·
            refine ⟨35810182159682577552496277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23873454773121718368330851 35810182159682577552496277)
            ·
              refine ⟨1678602288735120822773263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35810182159682577552496277 1678602288735120822773263)
              ·
                refine ⟨2517903433102681234159895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678602288735120822773263 2517903433102681234159895)
                ·
                  refine ⟨3776855149654021851239843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517903433102681234159895 3776855149654021851239843)
                  ·
                    refine ⟨5665282724481032776859765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776855149654021851239843 5665282724481032776859765)
                    ·
                      refine ⟨531120255420096822830603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5665282724481032776859765 531120255420096822830603)
                      ·
                        rfl

theorem cell23_1034353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_1034353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034353 prefixEnd_1034353 := by exact prefixLift 1034353
  have htrace : WordTrace (prefixWord ++ tailWord_1034353) baseStart_1034353 baseEnd_1034353 := by
    simpa [prefixWord, tailWord_1034353, baseEnd_1034353] using wordTrace_append hprefix tailTrace_1034353
  have hstable : (prefixWord ++ tailWord_1034353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034353).length < 2 ^ (prefixWord ++ tailWord_1034353).sum := by decide
  have hdescent : baseEnd_1034353 < baseStart_1034353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034373 : List Nat := [1, 3, 1, 1, 5, 2, 2, 8]
def baseStart_1034373 : Nat := 118140960795 + 1034373 * 2 ^ 59
def prefixEnd_1034373 : Nat := 4983230072969 + 3 ^ 40 * 1034373 * 2
def baseEnd_1034373 : Nat := 19671500927155064614093

theorem tailTrace_1034373 : CollatzResearch.WordTrace tailWord_1034373 prefixEnd_1034373 19671500927155064614093 := by
  unfold tailWord_1034373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726682681650752689139773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25151121787767168459426515 37726682681650752689139773)
  ·
    refine ⟨14147506005619032258427415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37726682681650752689139773 14147506005619032258427415)
    ·
      refine ⟨21221259008428548387641123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14147506005619032258427415 21221259008428548387641123)
      ·
        refine ⟨31831888512642822581461685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21221259008428548387641123 31831888512642822581461685)
        ·
          refine ⟨2984239548060264617012033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31831888512642822581461685 2984239548060264617012033)
          ·
            refine ⟨2238179661045198462759025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984239548060264617012033 2238179661045198462759025)
            ·
              refine ⟨1678634745783898847069269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238179661045198462759025 1678634745783898847069269)
              ·
                refine ⟨19671500927155064614093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1678634745783898847069269 19671500927155064614093)
                ·
                  rfl

theorem cell23_1034373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 8].length) (baseStart_1034373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034373 prefixEnd_1034373 := by exact prefixLift 1034373
  have htrace : WordTrace (prefixWord ++ tailWord_1034373) baseStart_1034373 baseEnd_1034373 := by
    simpa [prefixWord, tailWord_1034373, baseEnd_1034373] using wordTrace_append hprefix tailTrace_1034373
  have hstable : (prefixWord ++ tailWord_1034373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034373).length < 2 ^ (prefixWord ++ tailWord_1034373).sum := by decide
  have hdescent : baseEnd_1034373 < baseStart_1034373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034400 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1034400 : Nat := 118140960795 + 1034400 * 2 ^ 59
def prefixEnd_1034400 : Nat := 4983230072969 + 3 ^ 40 * 1034400 * 2
def baseEnd_1034400 : Nat := 531144389010858138942887

theorem tailTrace_1034400 : CollatzResearch.WordTrace tailWord_1034400 prefixEnd_1034400 531144389010858138942887 := by
  unfold tailWord_1034400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863833726276468150186327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25151778301701957533581769 18863833726276468150186327)
  ·
    refine ⟨28295750589414702225279491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863833726276468150186327 28295750589414702225279491)
    ·
      refine ⟨42443625884122053337919237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295750589414702225279491 42443625884122053337919237)
      ·
        refine ⟨7958179853272885000859857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42443625884122053337919237 7958179853272885000859857)
        ·
          refine ⟨5968634889954663750644893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7958179853272885000859857 5968634889954663750644893)
          ·
            refine ⟨2238238083732998906491835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5968634889954663750644893 2238238083732998906491835)
            ·
              refine ⟨3357357125599498359737753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238238083732998906491835 3357357125599498359737753)
              ·
                refine ⟨2518017844199623769803315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357357125599498359737753 2518017844199623769803315)
                ·
                  refine ⟨3777026766299435654704973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518017844199623769803315 3777026766299435654704973)
                  ·
                    refine ⟨1416385037362288370514365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777026766299435654704973 1416385037362288370514365)
                    ·
                      refine ⟨531144389010858138942887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416385037362288370514365 531144389010858138942887)
                      ·
                        rfl

theorem cell23_1034400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1034400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034400 prefixEnd_1034400 := by exact prefixLift 1034400
  have htrace : WordTrace (prefixWord ++ tailWord_1034400) baseStart_1034400 baseEnd_1034400 := by
    simpa [prefixWord, tailWord_1034400, baseEnd_1034400] using wordTrace_append hprefix tailTrace_1034400
  have hstable : (prefixWord ++ tailWord_1034400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034400).length < 2 ^ (prefixWord ++ tailWord_1034400).sum := by decide
  have hdescent : baseEnd_1034400 < baseStart_1034400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034404 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_1034404 : Nat := 118140960795 + 1034404 * 2 ^ 59
def prefixEnd_1034404 : Nat := 4983230072969 + 3 ^ 40 * 1034404 * 2
def baseEnd_1034404 : Nat := 531146442933476123292869

theorem tailTrace_1034404 : CollatzResearch.WordTrace tailWord_1034404 prefixEnd_1034404 531146442933476123292869 := by
  unfold tailWord_1034404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863906672269222491759133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25151875563025629989012177 18863906672269222491759133)
  ·
    refine ⟨7073965002100958434409675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18863906672269222491759133 7073965002100958434409675)
    ·
      refine ⟨10610947503151437651614513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073965002100958434409675 10610947503151437651614513)
      ·
        refine ⟨7958210627363578238710885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10610947503151437651614513 7958210627363578238710885)
        ·
          refine ⟨1492164492630670919758291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7958210627363578238710885 1492164492630670919758291)
          ·
            refine ⟨2238246738946006379637437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492164492630670919758291 2238246738946006379637437)
            ·
              refine ⟨839342527104752392364039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2238246738946006379637437 839342527104752392364039)
              ·
                refine ⟨1259013790657128588546059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839342527104752392364039 1259013790657128588546059)
                ·
                  refine ⟨1888520685985692882819089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259013790657128588546059 1888520685985692882819089)
                  ·
                    refine ⟨1416390514489269662114317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1888520685985692882819089 1416390514489269662114317)
                    ·
                      refine ⟨531146442933476123292869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416390514489269662114317 531146442933476123292869)
                      ·
                        rfl

theorem cell23_1034404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_1034404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034404 prefixEnd_1034404 := by exact prefixLift 1034404
  have htrace : WordTrace (prefixWord ++ tailWord_1034404) baseStart_1034404 baseEnd_1034404 := by
    simpa [prefixWord, tailWord_1034404, baseEnd_1034404] using wordTrace_append hprefix tailTrace_1034404
  have hstable : (prefixWord ++ tailWord_1034404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034404).length < 2 ^ (prefixWord ++ tailWord_1034404).sum := by decide
  have hdescent : baseEnd_1034404 < baseStart_1034404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034423 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1034423 : Nat := 118140960795 + 1034423 * 2 ^ 59
def prefixEnd_1034423 : Nat := 4983230072969 + 3 ^ 40 * 1034423 * 2
def baseEnd_1034423 : Nat := 531156199065911548955281

theorem tailTrace_1034423 : CollatzResearch.WordTrace tailWord_1034423 prefixEnd_1034423 531156199065911548955281 := by
  unfold tailWord_1034423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37728506331469611228459923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152337554313074152306615 37728506331469611228459923)
  ·
    refine ⟨56592759497204416842689885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37728506331469611228459923 56592759497204416842689885)
    ·
      refine ⟨21222284811451656316008707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56592759497204416842689885 21222284811451656316008707)
      ·
        refine ⟨31833427217177484474013061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21222284811451656316008707 31833427217177484474013061)
        ·
          refine ⟨5968767603220778338877449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31833427217177484474013061 5968767603220778338877449)
          ·
            refine ⟨4476575702415583754158087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5968767603220778338877449 4476575702415583754158087)
            ·
              refine ⟨6714863553623375631237131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476575702415583754158087 6714863553623375631237131)
              ·
                refine ⟨10072295330435063446855697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714863553623375631237131 10072295330435063446855697)
                ·
                  refine ⟨7554221497826297585141773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072295330435063446855697 7554221497826297585141773)
                  ·
                    refine ⟨2832833061684861594428165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7554221497826297585141773 2832833061684861594428165)
                    ·
                      refine ⟨531156199065911548955281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2832833061684861594428165 531156199065911548955281)
                      ·
                        rfl

theorem cell23_1034423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1034423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034423 prefixEnd_1034423 := by exact prefixLift 1034423
  have htrace : WordTrace (prefixWord ++ tailWord_1034423) baseStart_1034423 baseEnd_1034423 := by
    simpa [prefixWord, tailWord_1034423, baseEnd_1034423] using wordTrace_append hprefix tailTrace_1034423
  have hstable : (prefixWord ++ tailWord_1034423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034423).length < 2 ^ (prefixWord ++ tailWord_1034423).sum := by decide
  have hdescent : baseEnd_1034423 < baseStart_1034423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034434 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1034434 : Nat := 118140960795 + 1034434 * 2 ^ 59
def prefixEnd_1034434 : Nat := 4983230072969 + 3 ^ 40 * 1034434 * 2
def baseEnd_1034434 : Nat := 531161847353111005917731

theorem tailTrace_1034434 : CollatzResearch.WordTrace tailWord_1034434 prefixEnd_1034434 531161847353111005917731 := by
  unfold tailWord_1034434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432226883607440026777589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25152605022953173404740237 9432226883607440026777589)
  ·
    refine ⟨884271270338197502510399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9432226883607440026777589 884271270338197502510399)
    ·
      refine ⟨1326406905507296253765599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884271270338197502510399 1326406905507296253765599)
      ·
        refine ⟨1989610358260944380648399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326406905507296253765599 1989610358260944380648399)
        ·
          refine ⟨2984415537391416570972599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989610358260944380648399 2984415537391416570972599)
          ·
            refine ⟨4476623306087124856458899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984415537391416570972599 4476623306087124856458899)
            ·
              refine ⟨6714934959130687284688349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476623306087124856458899 6714934959130687284688349)
              ·
                refine ⟨2518100609674007731758131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6714934959130687284688349 2518100609674007731758131)
                ·
                  refine ⟨3777150914511011597637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518100609674007731758131 3777150914511011597637197)
                  ·
                    refine ⟨1416431592941629349113949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777150914511011597637197 1416431592941629349113949)
                    ·
                      refine ⟨531161847353111005917731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416431592941629349113949 531161847353111005917731)
                      ·
                        rfl

theorem cell23_1034434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1034434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034434 prefixEnd_1034434 := by exact prefixLift 1034434
  have htrace : WordTrace (prefixWord ++ tailWord_1034434) baseStart_1034434 baseEnd_1034434 := by
    simpa [prefixWord, tailWord_1034434, baseEnd_1034434] using wordTrace_append hprefix tailTrace_1034434
  have hstable : (prefixWord ++ tailWord_1034434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034434).length < 2 ^ (prefixWord ++ tailWord_1034434).sum := by decide
  have hdescent : baseEnd_1034434 < baseStart_1034434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034443 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3]
def baseStart_1034443 : Nat := 118140960795 + 1034443 * 2 ^ 59
def prefixEnd_1034443 : Nat := 4983230072969 + 3 ^ 40 * 1034443 * 2
def baseEnd_1034443 : Nat := 531166468679001470705189

theorem tailTrace_1034443 : CollatzResearch.WordTrace tailWord_1034443 prefixEnd_1034443 531166468679001470705189 := by
  unfold tailWord_1034443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37729235791397154644187983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152823860931436429458655 37729235791397154644187983)
  ·
    refine ⟨56593853687095731966281975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37729235791397154644187983 56593853687095731966281975)
    ·
      refine ⟨84890780530643597949422963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56593853687095731966281975 84890780530643597949422963)
      ·
        refine ⟨127336170795965396924134445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84890780530643597949422963 127336170795965396924134445)
        ·
          refine ⟨47751064048487023846550417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127336170795965396924134445 47751064048487023846550417)
          ·
            refine ⟨35813298036365267884912813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47751064048487023846550417 35813298036365267884912813)
            ·
              refine ⟨13429986763636975456842305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35813298036365267884912813 13429986763636975456842305)
              ·
                refine ⟨10072490072727731592631729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13429986763636975456842305 10072490072727731592631729)
                ·
                  refine ⟨7554367554545798694473797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072490072727731592631729 7554367554545798694473797)
                  ·
                    refine ⟨1416443916477337255213837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554367554545798694473797 1416443916477337255213837)
                    ·
                      refine ⟨531166468679001470705189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416443916477337255213837 531166468679001470705189)
                      ·
                        rfl

theorem cell23_1034443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].length) (baseStart_1034443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034443 prefixEnd_1034443 := by exact prefixLift 1034443
  have htrace : WordTrace (prefixWord ++ tailWord_1034443) baseStart_1034443 baseEnd_1034443 := by
    simpa [prefixWord, tailWord_1034443, baseEnd_1034443] using wordTrace_append hprefix tailTrace_1034443
  have hstable : (prefixWord ++ tailWord_1034443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034443).length < 2 ^ (prefixWord ++ tailWord_1034443).sum := by decide
  have hdescent : baseEnd_1034443 < baseStart_1034443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034461 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1034461 : Nat := 118140960795 + 1034461 * 2 ^ 59
def prefixEnd_1034461 : Nat := 4983230072969 + 3 ^ 40 * 1034461 * 2
def baseEnd_1034461 : Nat := 531175711330782400280107

theorem tailTrace_1034461 : CollatzResearch.WordTrace tailWord_1034461 prefixEnd_1034461 531175711330782400280107 := by
  unfold tailWord_1034461
  simp only [CollatzResearch.WordTrace]
  refine ⟨37729892305331943718343237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25153261536887962478895491 37729892305331943718343237)
  ·
    refine ⟨7074354807249739447189357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37729892305331943718343237 7074354807249739447189357)
    ·
      refine ⟨2652883052718652292696009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7074354807249739447189357 2652883052718652292696009)
      ·
        refine ⟨1989662289538989219522007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652883052718652292696009 1989662289538989219522007)
        ·
          refine ⟨2984493434308483829283011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989662289538989219522007 2984493434308483829283011)
          ·
            refine ⟨4476740151462725743924517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984493434308483829283011 4476740151462725743924517)
            ·
              refine ⟨839388778399261076985847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4476740151462725743924517 839388778399261076985847)
              ·
                refine ⟨1259083167598891615478771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839388778399261076985847 1259083167598891615478771)
                ·
                  refine ⟨1888624751398337423218157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259083167598891615478771 1888624751398337423218157)
                  ·
                    refine ⟨708234281774376533706809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888624751398337423218157 708234281774376533706809)
                    ·
                      refine ⟨531175711330782400280107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708234281774376533706809 531175711330782400280107)
                      ·
                        rfl

theorem cell23_1034461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1034461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034461 prefixEnd_1034461 := by exact prefixLift 1034461
  have htrace : WordTrace (prefixWord ++ tailWord_1034461) baseStart_1034461 baseEnd_1034461 := by
    simpa [prefixWord, tailWord_1034461, baseEnd_1034461] using wordTrace_append hprefix tailTrace_1034461
  have hstable : (prefixWord ++ tailWord_1034461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034461).length < 2 ^ (prefixWord ++ tailWord_1034461).sum := by decide
  have hdescent : baseEnd_1034461 < baseStart_1034461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034473 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_1034473 : Nat := 118140960795 + 1034473 * 2 ^ 59
def prefixEnd_1034473 : Nat := 4983230072969 + 3 ^ 40 * 1034473 * 2
def baseEnd_1034473 : Nat := 531181873098636353330051

theorem tailTrace_1034473 : CollatzResearch.WordTrace tailWord_1034473 prefixEnd_1034473 531181873098636353330051 := by
  unfold tailWord_1034473
  simp only [CollatzResearch.WordTrace]
  refine ⟨37730329981288469767780073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25153553320858979845186715 37730329981288469767780073)
  ·
    refine ⟨28297747485966352325835055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37730329981288469767780073 28297747485966352325835055)
    ·
      refine ⟨42446621228949528488752583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28297747485966352325835055 42446621228949528488752583)
      ·
        refine ⟨63669931843424292733128875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42446621228949528488752583 63669931843424292733128875)
        ·
          refine ⟨95504897765136439099693313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63669931843424292733128875 95504897765136439099693313)
          ·
            refine ⟨71628673323852329324769985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95504897765136439099693313 71628673323852329324769985)
            ·
              refine ⟨53721504992889246993577489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71628673323852329324769985 53721504992889246993577489)
              ·
                refine ⟨40291128744666935245183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53721504992889246993577489 40291128744666935245183117)
                ·
                  refine ⟨15109173279250100716943669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40291128744666935245183117 15109173279250100716943669)
                  ·
                    refine ⟨1416484994929696942213469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15109173279250100716943669 1416484994929696942213469)
                    ·
                      refine ⟨531181873098636353330051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416484994929696942213469 531181873098636353330051)
                      ·
                        rfl

theorem cell23_1034473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_1034473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034473 prefixEnd_1034473 := by exact prefixLift 1034473
  have htrace : WordTrace (prefixWord ++ tailWord_1034473) baseStart_1034473 baseEnd_1034473 := by
    simpa [prefixWord, tailWord_1034473, baseEnd_1034473] using wordTrace_append hprefix tailTrace_1034473
  have hstable : (prefixWord ++ tailWord_1034473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034473).length < 2 ^ (prefixWord ++ tailWord_1034473).sum := by decide
  have hdescent : baseEnd_1034473 < baseStart_1034473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034490 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1034490 : Nat := 118140960795 + 1034490 * 2 ^ 59
def prefixEnd_1034490 : Nat := 4983230072969 + 3 ^ 40 * 1034490 * 2
def baseEnd_1034490 : Nat := 531190602269762786817473

theorem tailTrace_1034490 : CollatzResearch.WordTrace tailWord_1034490 prefixEnd_1034490 531190602269762786817473 := by
  unfold tailWord_1034490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432737505556720417787231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25153966681484587780765949 9432737505556720417787231)
  ·
    refine ⟨14149106258335080626680847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432737505556720417787231 14149106258335080626680847)
    ·
      refine ⟨21223659387502620940021271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149106258335080626680847 21223659387502620940021271)
      ·
        refine ⟨31835489081253931410031907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223659387502620940021271 31835489081253931410031907)
        ·
          refine ⟨47753233621880897115047861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31835489081253931410031907 47753233621880897115047861)
          ·
            refine ⟨4476865652051334104535737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47753233621880897115047861 4476865652051334104535737)
            ·
              refine ⟨3357649239038500578401803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476865652051334104535737 3357649239038500578401803)
              ·
                refine ⟨5036473858557750867602705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357649239038500578401803 5036473858557750867602705)
                ·
                  refine ⟨3777355393918313150702029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036473858557750867602705 3777355393918313150702029)
                  ·
                    refine ⟨1416508272719367431513261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777355393918313150702029 1416508272719367431513261)
                    ·
                      refine ⟨531190602269762786817473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416508272719367431513261 531190602269762786817473)
                      ·
                        rfl

theorem cell23_1034490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1034490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034490 prefixEnd_1034490 := by exact prefixLift 1034490
  have htrace : WordTrace (prefixWord ++ tailWord_1034490) baseStart_1034490 baseEnd_1034490 := by
    simpa [prefixWord, tailWord_1034490, baseEnd_1034490] using wordTrace_append hprefix tailTrace_1034490
  have hstable : (prefixWord ++ tailWord_1034490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034490).length < 2 ^ (prefixWord ++ tailWord_1034490).sum := by decide
  have hdescent : baseEnd_1034490 < baseStart_1034490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034510 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1034510 : Nat := 118140960795 + 1034510 * 2 ^ 59
def prefixEnd_1034510 : Nat := 4983230072969 + 3 ^ 40 * 1034510 * 2
def baseEnd_1034510 : Nat := 177066957294284236189127

theorem tailTrace_1034510 : CollatzResearch.WordTrace tailWord_1034510 prefixEnd_1034510 177066957294284236189127 := by
  unfold tailWord_1034510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716459935269303135859623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25154452988102950057917989 4716459935269303135859623)
  ·
    refine ⟨7074689902903954703789435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716459935269303135859623 7074689902903954703789435)
    ·
      refine ⟨10612034854355932055684153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074689902903954703789435 10612034854355932055684153)
      ·
        refine ⟨7959026140766949041763115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10612034854355932055684153 7959026140766949041763115)
        ·
          refine ⟨11938539211150423562644673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959026140766949041763115 11938539211150423562644673)
          ·
            refine ⟨8953904408362817671983505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11938539211150423562644673 8953904408362817671983505)
            ·
              refine ⟨6715428306272113253987629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953904408362817671983505 6715428306272113253987629)
              ·
                refine ⟨2518285614852042470245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6715428306272113253987629 2518285614852042470245361)
                ·
                  refine ⟨1888714211139031852684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518285614852042470245361 1888714211139031852684021)
                  ·
                    refine ⟨177066957294284236189127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1888714211139031852684021 177066957294284236189127)
                    ·
                      rfl

theorem cell23_1034510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1034510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034510 prefixEnd_1034510 := by exact prefixLift 1034510
  have htrace : WordTrace (prefixWord ++ tailWord_1034510) baseStart_1034510 baseEnd_1034510 := by
    simpa [prefixWord, tailWord_1034510, baseEnd_1034510] using wordTrace_append hprefix tailTrace_1034510
  have hstable : (prefixWord ++ tailWord_1034510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034510).length < 2 ^ (prefixWord ++ tailWord_1034510).sum := by decide
  have hdescent : baseEnd_1034510 < baseStart_1034510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034542 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1034542 : Nat := 118140960795 + 1034542 * 2 ^ 59
def prefixEnd_1034542 : Nat := 4983230072969 + 3 ^ 40 * 1034542 * 2
def baseEnd_1034542 : Nat := 531217303263796583367235

theorem tailTrace_1034542 : CollatzResearch.WordTrace tailWord_1034542 prefixEnd_1034542 531217303263796583367235 := by
  unfold tailWord_1034542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716605827254811819005235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25155231078692329701361253 4716605827254811819005235)
  ·
    refine ⟨7074908740882217728507853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716605827254811819005235 7074908740882217728507853)
    ·
      refine ⟨2653090777830831648190445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7074908740882217728507853 2653090777830831648190445)
      ·
        refine ⟨994909041686561868071417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2653090777830831648190445 994909041686561868071417)
        ·
          refine ⟨746181781264921401053563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994909041686561868071417 746181781264921401053563)
          ·
            refine ⟨1119272671897382101580345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746181781264921401053563 1119272671897382101580345)
            ·
              refine ⟨839454503923036576185259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119272671897382101580345 839454503923036576185259)
              ·
                refine ⟨1259181755884554864277889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839454503923036576185259 1259181755884554864277889)
                ·
                  refine ⟨944386316913416148208417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1259181755884554864277889 944386316913416148208417)
                  ·
                    refine ⟨708289737685062111156313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944386316913416148208417 708289737685062111156313)
                    ·
                      refine ⟨531217303263796583367235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708289737685062111156313 531217303263796583367235)
                      ·
                        rfl

theorem cell23_1034542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1034542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034542 prefixEnd_1034542 := by exact prefixLift 1034542
  have htrace : WordTrace (prefixWord ++ tailWord_1034542) baseStart_1034542 baseEnd_1034542 := by
    simpa [prefixWord, tailWord_1034542, baseEnd_1034542] using wordTrace_append hprefix tailTrace_1034542
  have hstable : (prefixWord ++ tailWord_1034542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034542).length < 2 ^ (prefixWord ++ tailWord_1034542).sum := by decide
  have hdescent : baseEnd_1034542 < baseStart_1034542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034543 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1034543 : Nat := 118140960795 + 1034543 * 2 ^ 59
def prefixEnd_1034543 : Nat := 4983230072969 + 3 ^ 40 * 1034543 * 2
def baseEnd_1034543 : Nat := 531217816744451079454729

theorem tailTrace_1034543 : CollatzResearch.WordTrace tailWord_1034543 prefixEnd_1034543 531217816744451079454729 := by
  unfold tailWord_1034543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732883091034871722828283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25155255394023247815218855 37732883091034871722828283)
  ·
    refine ⟨56599324636552307584242425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37732883091034871722828283 56599324636552307584242425)
    ·
      refine ⟨42449493477414230688181819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56599324636552307584242425 42449493477414230688181819)
      ·
        refine ⟨63674240216121346032272729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42449493477414230688181819 63674240216121346032272729)
        ·
          refine ⟨47755680162091009524204547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63674240216121346032272729 47755680162091009524204547)
          ·
            refine ⟨71633520243136514286306821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47755680162091009524204547 71633520243136514286306821)
            ·
              refine ⟨13431285045588096428682529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71633520243136514286306821 13431285045588096428682529)
              ·
                refine ⟨10073463784191072321511897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431285045588096428682529 10073463784191072321511897)
                ·
                  refine ⟨7555097838143304241133923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073463784191072321511897 7555097838143304241133923)
                  ·
                    refine ⟨11332646757214956361700885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555097838143304241133923 11332646757214956361700885)
                    ·
                      refine ⟨531217816744451079454729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11332646757214956361700885 531217816744451079454729)
                      ·
                        rfl

theorem cell23_1034543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1034543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034543 prefixEnd_1034543 := by exact prefixLift 1034543
  have htrace : WordTrace (prefixWord ++ tailWord_1034543) baseStart_1034543 baseEnd_1034543 := by
    simpa [prefixWord, tailWord_1034543, baseEnd_1034543] using wordTrace_append hprefix tailTrace_1034543
  have hstable : (prefixWord ++ tailWord_1034543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034543).length < 2 ^ (prefixWord ++ tailWord_1034543).sum := by decide
  have hdescent : baseEnd_1034543 < baseStart_1034543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034567 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1034567 : Nat := 118140960795 + 1034567 * 2 ^ 59
def prefixEnd_1034567 : Nat := 4983230072969 + 3 ^ 40 * 1034567 * 2
def baseEnd_1034567 : Nat := 531230140280158985554619

theorem tailTrace_1034567 : CollatzResearch.WordTrace tailWord_1034567 prefixEnd_1034567 531230140280158985554619 := by
  unfold tailWord_1034567
  simp only [CollatzResearch.WordTrace]
  refine ⟨37733758442947923821701955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25155838961965282547801303 37733758442947923821701955)
  ·
    refine ⟨56600637664421885732552933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37733758442947923821701955 56600637664421885732552933)
    ·
      refine ⟨10612619562079103574853675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56600637664421885732552933 10612619562079103574853675)
      ·
        refine ⟨15918929343118655362280513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612619562079103574853675 15918929343118655362280513)
        ·
          refine ⟨11939197007338991521710385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15918929343118655362280513 11939197007338991521710385)
          ·
            refine ⟨8954397755504243641282789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11939197007338991521710385 8954397755504243641282789)
            ·
              refine ⟨1678949579157045682740523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8954397755504243641282789 1678949579157045682740523)
              ·
                refine ⟨2518424368735568524110785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678949579157045682740523 2518424368735568524110785)
                ·
                  refine ⟨1888818276551676393083089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518424368735568524110785 1888818276551676393083089)
                  ·
                    refine ⟨1416613707413757294812317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1888818276551676393083089 1416613707413757294812317)
                    ·
                      refine ⟨531230140280158985554619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416613707413757294812317 531230140280158985554619)
                      ·
                        rfl

theorem cell23_1034567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1034567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034567 prefixEnd_1034567 := by exact prefixLift 1034567
  have htrace : WordTrace (prefixWord ++ tailWord_1034567) baseStart_1034567 baseEnd_1034567 := by
    simpa [prefixWord, tailWord_1034567, baseEnd_1034567] using wordTrace_append hprefix tailTrace_1034567
  have hstable : (prefixWord ++ tailWord_1034567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034567).length < 2 ^ (prefixWord ++ tailWord_1034567).sum := by decide
  have hdescent : baseEnd_1034567 < baseStart_1034567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034631 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_1034631 : Nat := 118140960795 + 1034631 * 2 ^ 59
def prefixEnd_1034631 : Nat := 4983230072969 + 3 ^ 40 * 1034631 * 2
def baseEnd_1034631 : Nat := 531263003042046735154325

theorem tailTrace_1034631 : CollatzResearch.WordTrace tailWord_1034631 prefixEnd_1034631 531263003042046735154325 := by
  unfold tailWord_1034631
  simp only [CollatzResearch.WordTrace]
  refine ⟨37736092714716062752031747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25157395143144041834687831 37736092714716062752031747)
  ·
    refine ⟨56604139072074094128047621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37736092714716062752031747 56604139072074094128047621)
    ·
      refine ⟨10613276076013892649008929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56604139072074094128047621 10613276076013892649008929)
      ·
        refine ⟨7959957057010419486756697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10613276076013892649008929 7959957057010419486756697)
        ·
          refine ⟨5969967792757814615067523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7959957057010419486756697 5969967792757814615067523)
          ·
            refine ⟨8954951689136721922601285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969967792757814615067523 8954951689136721922601285)
            ·
              refine ⟨1679053441713135360487741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8954951689136721922601285 1679053441713135360487741)
              ·
                refine ⟨629645040642425760182903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679053441713135360487741 629645040642425760182903)
                ·
                  refine ⟨944467560963638640274355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629645040642425760182903 944467560963638640274355)
                  ·
                    refine ⟨1416701341445457960411533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944467560963638640274355 1416701341445457960411533)
                    ·
                      refine ⟨531263003042046735154325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416701341445457960411533 531263003042046735154325)
                      ·
                        rfl

theorem cell23_1034631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_1034631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034631 prefixEnd_1034631 := by exact prefixLift 1034631
  have htrace : WordTrace (prefixWord ++ tailWord_1034631) baseStart_1034631 baseEnd_1034631 := by
    simpa [prefixWord, tailWord_1034631, baseEnd_1034631] using wordTrace_append hprefix tailTrace_1034631
  have hstable : (prefixWord ++ tailWord_1034631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034631).length < 2 ^ (prefixWord ++ tailWord_1034631).sum := by decide
  have hdescent : baseEnd_1034631 < baseStart_1034631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034664 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1034664 : Nat := 118140960795 + 1034664 * 2 ^ 59
def prefixEnd_1034664 : Nat := 4983230072969 + 3 ^ 40 * 1034664 * 2
def baseEnd_1034664 : Nat := 177093315967881702013891

theorem tailTrace_1034664 : CollatzResearch.WordTrace tailWord_1034664 prefixEnd_1034664 177093315967881702013891 := by
  unfold tailWord_1034664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868648161798254693991523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25158197549064339591988697 18868648161798254693991523)
  ·
    refine ⟨28302972242697382040987285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18868648161798254693991523 28302972242697382040987285)
    ·
      refine ⟨1326701823876439783171279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28302972242697382040987285 1326701823876439783171279)
      ·
        refine ⟨1990052735814659674756919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326701823876439783171279 1990052735814659674756919)
        ·
          refine ⟨2985079103721989512135379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990052735814659674756919 2985079103721989512135379)
          ·
            refine ⟨4477618655582984268203069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985079103721989512135379 4477618655582984268203069)
            ·
              refine ⟨1679106995843619100576151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4477618655582984268203069 1679106995843619100576151)
              ·
                refine ⟨2518660493765428650864227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679106995843619100576151 2518660493765428650864227)
                ·
                  refine ⟨3777990740648142976296341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518660493765428650864227 3777990740648142976296341)
                  ·
                    refine ⟨177093315967881702013891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3777990740648142976296341 177093315967881702013891)
                    ·
                      rfl

theorem cell23_1034664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1034664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034664 prefixEnd_1034664 := by exact prefixLift 1034664
  have htrace : WordTrace (prefixWord ++ tailWord_1034664) baseStart_1034664 baseEnd_1034664 := by
    simpa [prefixWord, tailWord_1034664, baseEnd_1034664] using wordTrace_append hprefix tailTrace_1034664
  have hstable : (prefixWord ++ tailWord_1034664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034664).length < 2 ^ (prefixWord ++ tailWord_1034664).sum := by decide
  have hdescent : baseEnd_1034664 < baseStart_1034664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034674 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1034674 : Nat := 118140960795 + 1034674 * 2 ^ 59
def prefixEnd_1034674 : Nat := 4983230072969 + 3 ^ 40 * 1034674 * 2
def baseEnd_1034674 : Nat := 531285082710190066916627

theorem tailTrace_1034674 : CollatzResearch.WordTrace tailWord_1034674 prefixEnd_1034674 531285082710190066916627 := by
  unfold tailWord_1034674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434415263390070273961769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25158440702373520730564717 9434415263390070273961769)
  ·
    refine ⟨7075811447542552705471327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9434415263390070273961769 7075811447542552705471327)
    ·
      refine ⟨10613717171313829058206991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075811447542552705471327 10613717171313829058206991)
      ·
        refine ⟨15920575756970743587310487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613717171313829058206991 15920575756970743587310487)
        ·
          refine ⟨23880863635456115380965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15920575756970743587310487 23880863635456115380965731)
          ·
            refine ⟨35821295453184173071448597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23880863635456115380965731 35821295453184173071448597)
            ·
              refine ⟨1679123224368008112724153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35821295453184173071448597 1679123224368008112724153)
              ·
                refine ⟨1259342418276006084543115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679123224368008112724153 1259342418276006084543115)
                ·
                  refine ⟨1889013627414009126814673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259342418276006084543115 1889013627414009126814673)
                  ·
                    refine ⟨1416760220560506845111005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889013627414009126814673 1416760220560506845111005)
                    ·
                      refine ⟨531285082710190066916627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416760220560506845111005 531285082710190066916627)
                      ·
                        rfl

theorem cell23_1034674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1034674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034674 prefixEnd_1034674 := by exact prefixLift 1034674
  have htrace : WordTrace (prefixWord ++ tailWord_1034674) baseStart_1034674 baseEnd_1034674 := by
    simpa [prefixWord, tailWord_1034674, baseEnd_1034674] using wordTrace_append hprefix tailTrace_1034674
  have hstable : (prefixWord ++ tailWord_1034674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034674).length < 2 ^ (prefixWord ++ tailWord_1034674).sum := by decide
  have hdescent : baseEnd_1034674 < baseStart_1034674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034677 : List Nat := [1, 3, 3, 2, 3, 1, 1, 9]
def baseStart_1034677 : Nat := 118140960795 + 1034677 * 2 ^ 59
def prefixEnd_1034677 : Nat := 4983230072969 + 3 ^ 40 * 1034677 * 2
def baseEnd_1034677 : Nat := 19677282338968650191819

theorem tailTrace_1034677 : CollatzResearch.WordTrace tailWord_1034677 prefixEnd_1034677 19677282338968650191819 := by
  unfold tailWord_1034677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737770472549412608206285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25158513648366275072137523 37737770472549412608206285)
  ·
    refine ⟨14151663927206029728077357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37737770472549412608206285 14151663927206029728077357)
    ·
      refine ⟨5306873972702261148029009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14151663927206029728077357 5306873972702261148029009)
      ·
        refine ⟨3980155479526695861021757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5306873972702261148029009 3980155479526695861021757)
        ·
          refine ⟨1492558304822510947883159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3980155479526695861021757 1492558304822510947883159)
          ·
            refine ⟨2238837457233766421824739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492558304822510947883159 2238837457233766421824739)
            ·
              refine ⟨3358256185850649632737109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238837457233766421824739 3358256185850649632737109)
              ·
                refine ⟨19677282338968650191819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3358256185850649632737109 19677282338968650191819)
                ·
                  rfl

theorem cell23_1034677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 9].length) (baseStart_1034677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034677 prefixEnd_1034677 := by exact prefixLift 1034677
  have htrace : WordTrace (prefixWord ++ tailWord_1034677) baseStart_1034677 baseEnd_1034677 := by
    simpa [prefixWord, tailWord_1034677, baseEnd_1034677] using wordTrace_append hprefix tailTrace_1034677
  have hstable : (prefixWord ++ tailWord_1034677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034677).length < 2 ^ (prefixWord ++ tailWord_1034677).sum := by decide
  have hdescent : baseEnd_1034677 < baseStart_1034677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034714 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_1034714 : Nat := 118140960795 + 1034714 * 2 ^ 59
def prefixEnd_1034714 : Nat := 4983230072969 + 3 ^ 40 * 1034714 * 2
def baseEnd_1034714 : Nat := 531305621936369910416443

theorem tailTrace_1034714 : CollatzResearch.WordTrace tailWord_1034714 prefixEnd_1034714 531305621936369910416443 := by
  unfold tailWord_1034714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434779993353841981825799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25159413315610245284868797 9434779993353841981825799)
  ·
    refine ⟨14152169990030762972738699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9434779993353841981825799 14152169990030762972738699)
    ·
      refine ⟨21228254985046144459108049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14152169990030762972738699 21228254985046144459108049)
      ·
        refine ⟨15921191238784608344331037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21228254985046144459108049 15921191238784608344331037)
        ·
          refine ⟨5970446714544228129124139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15921191238784608344331037 5970446714544228129124139)
          ·
            refine ⟨8955670071816342193686209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970446714544228129124139 8955670071816342193686209)
            ·
              refine ⟨6716752553862256645264657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955670071816342193686209 6716752553862256645264657)
              ·
                refine ⟨5037564415396692483948493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716752553862256645264657 5037564415396692483948493)
                ·
                  refine ⟨1889086655773759681480685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5037564415396692483948493 1889086655773759681480685)
                  ·
                    refine ⟨708407495915159880555257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889086655773759681480685 708407495915159880555257)
                    ·
                      refine ⟨531305621936369910416443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708407495915159880555257 531305621936369910416443)
                      ·
                        rfl

theorem cell23_1034714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_1034714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034714 prefixEnd_1034714 := by exact prefixLift 1034714
  have htrace : WordTrace (prefixWord ++ tailWord_1034714) baseStart_1034714 baseEnd_1034714 := by
    simpa [prefixWord, tailWord_1034714, baseEnd_1034714] using wordTrace_append hprefix tailTrace_1034714
  have hstable : (prefixWord ++ tailWord_1034714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034714).length < 2 ^ (prefixWord ++ tailWord_1034714).sum := by decide
  have hdescent : baseEnd_1034714 < baseStart_1034714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034720 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_1034720 : Nat := 118140960795 + 1034720 * 2 ^ 59
def prefixEnd_1034720 : Nat := 4983230072969 + 3 ^ 40 * 1034720 * 2
def baseEnd_1034720 : Nat := 177102900940098962313805

theorem tailTrace_1034720 : CollatzResearch.WordTrace tailWord_1034720 prefixEnd_1034720 177102900940098962313805 := by
  unfold tailWord_1034720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869669405696815476010807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25159559207595753968014409 18869669405696815476010807)
  ·
    refine ⟨28304504108545223214016211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18869669405696815476010807 28304504108545223214016211)
    ·
      refine ⟨42456756162817834821024317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28304504108545223214016211 42456756162817834821024317)
      ·
        refine ⟨15921283561056688057884119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42456756162817834821024317 15921283561056688057884119)
        ·
          refine ⟨23881925341585032086826179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15921283561056688057884119 23881925341585032086826179)
          ·
            refine ⟨35822888012377548130239269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881925341585032086826179 35822888012377548130239269)
            ·
              refine ⟨6716791502320790274419863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35822888012377548130239269 6716791502320790274419863)
              ·
                refine ⟨10075187253481185411629795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716791502320790274419863 10075187253481185411629795)
                ·
                  refine ⟨15112780880221778117444693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075187253481185411629795 15112780880221778117444693)
                  ·
                    refine ⟨177102900940098962313805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15112780880221778117444693 177102900940098962313805)
                    ·
                      rfl

theorem cell23_1034720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_1034720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034720 prefixEnd_1034720 := by exact prefixLift 1034720
  have htrace : WordTrace (prefixWord ++ tailWord_1034720) baseStart_1034720 baseEnd_1034720 := by
    simpa [prefixWord, tailWord_1034720, baseEnd_1034720] using wordTrace_append hprefix tailTrace_1034720
  have hstable : (prefixWord ++ tailWord_1034720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034720).length < 2 ^ (prefixWord ++ tailWord_1034720).sum := by decide
  have hdescent : baseEnd_1034720 < baseStart_1034720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034744 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_1034744 : Nat := 118140960795 + 1034744 * 2 ^ 59
def prefixEnd_1034744 : Nat := 4983230072969 + 3 ^ 40 * 1034744 * 2
def baseEnd_1034744 : Nat := 531321026356004793041305

theorem tailTrace_1034744 : CollatzResearch.WordTrace tailWord_1034744 prefixEnd_1034744 531321026356004793041305 := by
  unfold tailWord_1034744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870107081653341525447643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25160142775537788700596857 18870107081653341525447643)
  ·
    refine ⟨28305160622480012288171465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18870107081653341525447643 28305160622480012288171465)
    ·
      refine ⟨21228870466860009216128599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28305160622480012288171465 21228870466860009216128599)
      ·
        refine ⟨31843305700290013824192899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21228870466860009216128599 31843305700290013824192899)
        ·
          refine ⟨47764958550435020736289349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31843305700290013824192899 47764958550435020736289349)
          ·
            refine ⟨8955929728206566388054253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47764958550435020736289349 8955929728206566388054253)
            ·
              refine ⟨3358473648077462395520345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8955929728206566388054253 3358473648077462395520345)
              ·
                refine ⟨2518855236058096796640259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358473648077462395520345 2518855236058096796640259)
                ·
                  refine ⟨3778282854087145194960389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518855236058096796640259 3778282854087145194960389)
                  ·
                    refine ⟨708428035141339724055073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778282854087145194960389 708428035141339724055073)
                    ·
                      refine ⟨531321026356004793041305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708428035141339724055073 531321026356004793041305)
                      ·
                        rfl

theorem cell23_1034744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_1034744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034744 prefixEnd_1034744 := by exact prefixLift 1034744
  have htrace : WordTrace (prefixWord ++ tailWord_1034744) baseStart_1034744 baseEnd_1034744 := by
    simpa [prefixWord, tailWord_1034744, baseEnd_1034744] using wordTrace_append hprefix tailTrace_1034744
  have hstable : (prefixWord ++ tailWord_1034744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034744).length < 2 ^ (prefixWord ++ tailWord_1034744).sum := by decide
  have hdescent : baseEnd_1034744 < baseStart_1034744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034777 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_1034777 : Nat := 118140960795 + 1034777 * 2 ^ 59
def prefixEnd_1034777 : Nat := 4983230072969 + 3 ^ 40 * 1034777 * 2
def baseEnd_1034777 : Nat := 531337971217603163928653

theorem tailTrace_1034777 : CollatzResearch.WordTrace tailWord_1034777 prefixEnd_1034777 531337971217603163928653 := by
  unfold tailWord_1034777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37741417772187129686846585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25160945181458086457897723 37741417772187129686846585)
  ·
    refine ⟨28306063329140347265134939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37741417772187129686846585 28306063329140347265134939)
    ·
      refine ⟨42459094993710520897702409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306063329140347265134939 42459094993710520897702409)
      ·
        refine ⟨31844321245282890673276807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42459094993710520897702409 31844321245282890673276807)
        ·
          refine ⟨47766481867924336009915211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31844321245282890673276807 47766481867924336009915211)
          ·
            refine ⟨71649722801886504014872817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47766481867924336009915211 71649722801886504014872817)
            ·
              refine ⟨53737292101414878011154613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71649722801886504014872817 53737292101414878011154613)
              ·
                refine ⟨5037871134507644813545745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53737292101414878011154613 5037871134507644813545745)
                ·
                  refine ⟨3778403350880733610159309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037871134507644813545745 3778403350880733610159309)
                  ·
                    refine ⟨1416901256580275103809741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778403350880733610159309 1416901256580275103809741)
                    ·
                      refine ⟨531337971217603163928653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1416901256580275103809741 531337971217603163928653)
                      ·
                        rfl

theorem cell23_1034777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_1034777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034777 prefixEnd_1034777 := by exact prefixLift 1034777
  have htrace : WordTrace (prefixWord ++ tailWord_1034777) baseStart_1034777 baseEnd_1034777 := by
    simpa [prefixWord, tailWord_1034777, baseEnd_1034777] using wordTrace_append hprefix tailTrace_1034777
  have hstable : (prefixWord ++ tailWord_1034777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034777).length < 2 ^ (prefixWord ++ tailWord_1034777).sum := by decide
  have hdescent : baseEnd_1034777 < baseStart_1034777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034784 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 7]
def baseStart_1034784 : Nat := 118140960795 + 1034784 * 2 ^ 59
def prefixEnd_1034784 : Nat := 4983230072969 + 3 ^ 40 * 1034784 * 2
def baseEnd_1034784 : Nat := 59037951731353848504569

theorem tailTrace_1034784 : CollatzResearch.WordTrace tailWord_1034784 prefixEnd_1034784 59037951731353848504569 := by
  unfold tailWord_1034784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870836541580884941175703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25161115388774513254900937 18870836541580884941175703)
  ·
    refine ⟨28306254812371327411763555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18870836541580884941175703 28306254812371327411763555)
    ·
      refine ⟨42459382218556991117645333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306254812371327411763555 42459382218556991117645333)
      ·
        refine ⟨1990283541494858958639625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42459382218556991117645333 1990283541494858958639625)
        ·
          refine ⟨1492712656121144218979719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990283541494858958639625 1492712656121144218979719)
          ·
            refine ⟨2239068984181716328469579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492712656121144218979719 2239068984181716328469579)
            ·
              refine ⟨3358603476272574492704369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239068984181716328469579 3358603476272574492704369)
              ·
                refine ⟨2518952607204430869528277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358603476272574492704369 2518952607204430869528277)
                ·
                  refine ⟨59037951731353848504569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2518952607204430869528277 59037951731353848504569)
                  ·
                    rfl

theorem cell23_1034784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_1034784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034784 prefixEnd_1034784 := by exact prefixLift 1034784
  have htrace : WordTrace (prefixWord ++ tailWord_1034784) baseStart_1034784 baseEnd_1034784 := by
    simpa [prefixWord, tailWord_1034784, baseEnd_1034784] using wordTrace_append hprefix tailTrace_1034784
  have hstable : (prefixWord ++ tailWord_1034784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034784).length < 2 ^ (prefixWord ++ tailWord_1034784).sum := by decide
  have hdescent : baseEnd_1034784 < baseStart_1034784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034904 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1034904 : Nat := 118140960795 + 1034904 * 2 ^ 59
def prefixEnd_1034904 : Nat := 4983230072969 + 3 ^ 40 * 1034904 * 2
def baseEnd_1034904 : Nat := 177134394420241389013523

theorem tailTrace_1034904 : CollatzResearch.WordTrace tailWord_1034904 prefixEnd_1034904 177134394420241389013523 := by
  unfold tailWord_1034904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873024921363515188359883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25164033228484686917813177 18873024921363515188359883)
  ·
    refine ⟨28309537382045272782539825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18873024921363515188359883 28309537382045272782539825)
    ·
      refine ⟨21232153036533954586904869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28309537382045272782539825 21232153036533954586904869)
      ·
        refine ⟨3981028694350116485044663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21232153036533954586904869 3981028694350116485044663)
        ·
          refine ⟨5971543041525174727566995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981028694350116485044663 5971543041525174727566995)
          ·
            refine ⟨8957314562287762091350493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971543041525174727566995 8957314562287762091350493)
            ·
              refine ⟨3358992960857910784256435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8957314562287762091350493 3358992960857910784256435)
              ·
                refine ⟨5038489441286866176384653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358992960857910784256435 5038489441286866176384653)
                ·
                  refine ⟨1889433540482574816144245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5038489441286866176384653 1889433540482574816144245)
                  ·
                    refine ⟨177134394420241389013523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1889433540482574816144245 177134394420241389013523)
                    ·
                      rfl

theorem cell23_1034904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1034904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034904 prefixEnd_1034904 := by exact prefixLift 1034904
  have htrace : WordTrace (prefixWord ++ tailWord_1034904) baseStart_1034904 baseEnd_1034904 := by
    simpa [prefixWord, tailWord_1034904, baseEnd_1034904] using wordTrace_append hprefix tailTrace_1034904
  have hstable : (prefixWord ++ tailWord_1034904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034904).length < 2 ^ (prefixWord ++ tailWord_1034904).sum := by decide
  have hdescent : baseEnd_1034904 < baseStart_1034904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034929 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1034929 : Nat := 118140960795 + 1034929 * 2 ^ 59
def prefixEnd_1034929 : Nat := 4983230072969 + 3 ^ 40 * 1034929 * 2
def baseEnd_1034929 : Nat := 177138673425695523075985

theorem tailTrace_1034929 : CollatzResearch.WordTrace tailWord_1034929 prefixEnd_1034929 177138673425695523075985 := by
  unfold tailWord_1034929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37746961667636459646379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25164641111757639764253227 37746961667636459646379841)
  ·
    refine ⟨28310221250727344734784881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37746961667636459646379841 28310221250727344734784881)
    ·
      refine ⟨21232665938045508551088661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28310221250727344734784881 21232665938045508551088661)
      ·
        refine ⟨995281215845883213332281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21232665938045508551088661 995281215845883213332281)
        ·
          refine ⟨746460911884412409999211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995281215845883213332281 746460911884412409999211)
          ·
            refine ⟨1119691367826618614998817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746460911884412409999211 1119691367826618614998817)
            ·
              refine ⟨839768525869963961249113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119691367826618614998817 839768525869963961249113)
              ·
                refine ⟨629826394402472970936835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839768525869963961249113 629826394402472970936835)
                ·
                  refine ⟨944739591603709456405253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629826394402472970936835 944739591603709456405253)
                  ·
                    refine ⟨177138673425695523075985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944739591603709456405253 177138673425695523075985)
                    ·
                      rfl

theorem cell23_1034929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1034929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034929 prefixEnd_1034929 := by exact prefixLift 1034929
  have htrace : WordTrace (prefixWord ++ tailWord_1034929) baseStart_1034929 baseEnd_1034929 := by
    simpa [prefixWord, tailWord_1034929, baseEnd_1034929] using wordTrace_append hprefix tailTrace_1034929
  have hstable : (prefixWord ++ tailWord_1034929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034929).length < 2 ^ (prefixWord ++ tailWord_1034929).sum := by decide
  have hdescent : baseEnd_1034929 < baseStart_1034929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034935 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_1034935 : Nat := 118140960795 + 1034935 * 2 ^ 59
def prefixEnd_1034935 : Nat := 4983230072969 + 3 ^ 40 * 1034935 * 2
def baseEnd_1034935 : Nat := 531419101161013545752927

theorem tailTrace_1034935 : CollatzResearch.WordTrace tailWord_1034935 prefixEnd_1034935 531419101161013545752927 := by
  unfold tailWord_1034935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37747180505614722671098259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25164787003743148447398839 37747180505614722671098259)
  ·
    refine ⟨56620770758422084006647389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37747180505614722671098259 56620770758422084006647389)
    ·
      refine ⟨21232789034408281502492771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56620770758422084006647389 21232789034408281502492771)
      ·
        refine ⟨31849183551612422253739157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232789034408281502492771 31849183551612422253739157)
        ·
          refine ⟨1492930478981832293144023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31849183551612422253739157 1492930478981832293144023)
          ·
            refine ⟨2239395718472748439716035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492930478981832293144023 2239395718472748439716035)
            ·
              refine ⟨3359093577709122659574053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239395718472748439716035 3359093577709122659574053)
              ·
                refine ⟨629830045820460498670135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3359093577709122659574053 629830045820460498670135)
                ·
                  refine ⟨944745068730690748005203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629830045820460498670135 944745068730690748005203)
                  ·
                    refine ⟨1417117603096036122007805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944745068730690748005203 1417117603096036122007805)
                    ·
                      refine ⟨531419101161013545752927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1417117603096036122007805 531419101161013545752927)
                      ·
                        rfl

theorem cell23_1034935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_1034935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034935 prefixEnd_1034935 := by exact prefixLift 1034935
  have htrace : WordTrace (prefixWord ++ tailWord_1034935) baseStart_1034935 baseEnd_1034935 := by
    simpa [prefixWord, tailWord_1034935, baseEnd_1034935] using wordTrace_append hprefix tailTrace_1034935
  have hstable : (prefixWord ++ tailWord_1034935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034935).length < 2 ^ (prefixWord ++ tailWord_1034935).sum := by decide
  have hdescent : baseEnd_1034935 < baseStart_1034935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034958 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_1034958 : Nat := 118140960795 + 1034958 * 2 ^ 59
def prefixEnd_1034958 : Nat := 4983230072969 + 3 ^ 40 * 1034958 * 2
def baseEnd_1034958 : Nat := 531430911216066955765321

theorem tailTrace_1034958 : CollatzResearch.WordTrace tailWord_1034958 prefixEnd_1034958 531430911216066955765321 := by
  unfold tailWord_1034958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718502423066424699898191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25165346256354265066123685 4718502423066424699898191)
  ·
    refine ⟨7077753634599637049847287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718502423066424699898191 7077753634599637049847287)
    ·
      refine ⟨10616630451899455574770931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7077753634599637049847287 10616630451899455574770931)
      ·
        refine ⟨15924945677849183362156397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616630451899455574770931 15924945677849183362156397)
        ·
          refine ⟨5971854629193443760808649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15924945677849183362156397 5971854629193443760808649)
          ·
            refine ⟨4478890971895082820606487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971854629193443760808649 4478890971895082820606487)
            ·
              refine ⟨6718336457842624230909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478890971895082820606487 6718336457842624230909731)
              ·
                refine ⟨10077504686763936346364597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718336457842624230909731 10077504686763936346364597)
                ·
                  refine ⟨944766064384119032471681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10077504686763936346364597 944766064384119032471681)
                  ·
                    refine ⟨708574548288089274353761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944766064384119032471681 708574548288089274353761)
                    ·
                      refine ⟨531430911216066955765321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708574548288089274353761 531430911216066955765321)
                      ·
                        rfl

theorem cell23_1034958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_1034958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034958 prefixEnd_1034958 := by exact prefixLift 1034958
  have htrace : WordTrace (prefixWord ++ tailWord_1034958) baseStart_1034958 baseEnd_1034958 := by
    simpa [prefixWord, tailWord_1034958, baseEnd_1034958] using wordTrace_append hprefix tailTrace_1034958
  have hstable : (prefixWord ++ tailWord_1034958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034958).length < 2 ^ (prefixWord ++ tailWord_1034958).sum := by decide
  have hdescent : baseEnd_1034958 < baseStart_1034958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034961 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_1034961 : Nat := 118140960795 + 1034961 * 2 ^ 59
def prefixEnd_1034961 : Nat := 4983230072969 + 3 ^ 40 * 1034961 * 2
def baseEnd_1034961 : Nat := 531432451658030444027807

theorem tailTrace_1034961 : CollatzResearch.WordTrace tailWord_1034961 prefixEnd_1034961 531432451658030444027807 := by
  unfold tailWord_1034961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37748128803520529111544737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25165419202347019407696491 37748128803520529111544737)
  ·
    refine ⟨28311096602640396833658553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37748128803520529111544737 28311096602640396833658553)
    ·
      refine ⟨21233322451980297625243915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28311096602640396833658553 21233322451980297625243915)
      ·
        refine ⟨31849983677970446437865873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21233322451980297625243915 31849983677970446437865873)
        ·
          refine ⟨23887487758477834828399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31849983677970446437865873 23887487758477834828399405)
          ·
            refine ⟨8957807909429188060649777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23887487758477834828399405 8957807909429188060649777)
            ·
              refine ⟨6718355932071891045487333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957807909429188060649777 6718355932071891045487333)
              ·
                refine ⟨1259691737263479571028875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6718355932071891045487333 1259691737263479571028875)
                ·
                  refine ⟨1889537605895219356543313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259691737263479571028875 1889537605895219356543313)
                  ·
                    refine ⟨1417153204421414517407485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889537605895219356543313 1417153204421414517407485)
                    ·
                      refine ⟨531432451658030444027807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1417153204421414517407485 531432451658030444027807)
                      ·
                        rfl

theorem cell23_1034961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_1034961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034961 prefixEnd_1034961 := by exact prefixLift 1034961
  have htrace : WordTrace (prefixWord ++ tailWord_1034961) baseStart_1034961 baseEnd_1034961 := by
    simpa [prefixWord, tailWord_1034961, baseEnd_1034961] using wordTrace_append hprefix tailTrace_1034961
  have hstable : (prefixWord ++ tailWord_1034961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034961).length < 2 ^ (prefixWord ++ tailWord_1034961).sum := by decide
  have hdescent : baseEnd_1034961 < baseStart_1034961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034962 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1034962 : Nat := 118140960795 + 1034962 * 2 ^ 59
def prefixEnd_1034962 : Nat := 4983230072969 + 3 ^ 40 * 1034962 * 2
def baseEnd_1034962 : Nat := 531432965138684940115303

theorem tailTrace_1034962 : CollatzResearch.WordTrace tailWord_1034962 prefixEnd_1034962 531432965138684940115303 := by
  unfold tailWord_1034962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437041319129226570582785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25165443517677937521554093 9437041319129226570582785)
  ·
    refine ⟨7077780989346919927937089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9437041319129226570582785 7077780989346919927937089)
    ·
      refine ⟨5308335742010189945952817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077780989346919927937089 5308335742010189945952817)
      ·
        refine ⟨3981251806507642459464613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308335742010189945952817 3981251806507642459464613)
        ·
          refine ⟨746484713720182961149615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3981251806507642459464613 746484713720182961149615)
          ·
            refine ⟨1119727070580274441724423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746484713720182961149615 1119727070580274441724423)
            ·
              refine ⟨1679590605870411662586635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119727070580274441724423 1679590605870411662586635)
              ·
                refine ⟨2519385908805617493879953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679590605870411662586635 2519385908805617493879953)
                ·
                  refine ⟨1889539431604213120409965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519385908805617493879953 1889539431604213120409965)
                  ·
                    refine ⟨708577286851579920153737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889539431604213120409965 708577286851579920153737)
                    ·
                      refine ⟨531432965138684940115303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708577286851579920153737 531432965138684940115303)
                      ·
                        rfl

theorem cell23_1034962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1034962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034962 prefixEnd_1034962 := by exact prefixLift 1034962
  have htrace : WordTrace (prefixWord ++ tailWord_1034962) baseStart_1034962 baseEnd_1034962 := by
    simpa [prefixWord, tailWord_1034962, baseEnd_1034962] using wordTrace_append hprefix tailTrace_1034962
  have hstable : (prefixWord ++ tailWord_1034962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034962).length < 2 ^ (prefixWord ++ tailWord_1034962).sum := by decide
  have hdescent : baseEnd_1034962 < baseStart_1034962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034975 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 1, 2, 2]
def baseStart_1034975 : Nat := 118140960795 + 1034975 * 2 ^ 59
def prefixEnd_1034975 : Nat := 4983230072969 + 3 ^ 40 * 1034975 * 2
def baseEnd_1034975 : Nat := 531439640387193389252743

theorem tailTrace_1034975 : CollatzResearch.WordTrace tailWord_1034975 prefixEnd_1034975 531439640387193389252743 := by
  unfold tailWord_1034975
  simp only [CollatzResearch.WordTrace]
  refine ⟨37748639425469809502554379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25165759616979873001702919 37748639425469809502554379)
  ·
    refine ⟨56622959138204714253831569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37748639425469809502554379 56622959138204714253831569)
    ·
      refine ⟨42467219353653535690373677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56622959138204714253831569 42467219353653535690373677)
      ·
        refine ⟨15925207257620075883890129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42467219353653535690373677 15925207257620075883890129)
        ·
          refine ⟨11943905443215056912917597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15925207257620075883890129 11943905443215056912917597)
          ·
            refine ⟨4478964541205646342344099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11943905443215056912917597 4478964541205646342344099)
            ·
              refine ⟨6718446811808469513516149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478964541205646342344099 6718446811808469513516149)
              ·
                refine ⟨629854388607044016892139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6718446811808469513516149 629854388607044016892139)
                ·
                  refine ⟨944781582910566025338209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629854388607044016892139 944781582910566025338209)
                  ·
                    refine ⟨708586187182924519003657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944781582910566025338209 708586187182924519003657)
                    ·
                      refine ⟨531439640387193389252743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708586187182924519003657 531439640387193389252743)
                      ·
                        rfl

theorem cell23_1034975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_1034975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1034975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1034975 prefixEnd_1034975 := by exact prefixLift 1034975
  have htrace : WordTrace (prefixWord ++ tailWord_1034975) baseStart_1034975 baseEnd_1034975 := by
    simpa [prefixWord, tailWord_1034975, baseEnd_1034975] using wordTrace_append hprefix tailTrace_1034975
  have hstable : (prefixWord ++ tailWord_1034975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034975).length < 2 ^ (prefixWord ++ tailWord_1034975).sum := by decide
  have hdescent : baseEnd_1034975 < baseStart_1034975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035001 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 5, 3, 2]
def baseStart_1035001 : Nat := 118140960795 + 1035001 * 2 ^ 59
def prefixEnd_1035001 : Nat := 4983230072969 + 3 ^ 40 * 1035001 * 2
def baseEnd_1035001 : Nat := 531452990884210287527623

theorem tailTrace_1035001 : CollatzResearch.WordTrace tailWord_1035001 prefixEnd_1035001 531452990884210287527623 := by
  unfold tailWord_1035001
  simp only [CollatzResearch.WordTrace]
  refine ⟨37749587723375615943000857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25166391815583743962000571 37749587723375615943000857)
  ·
    refine ⟨28312190792531711957250643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37749587723375615943000857 28312190792531711957250643)
    ·
      refine ⟨42468286188797567935875965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28312190792531711957250643 42468286188797567935875965)
      ·
        refine ⟨15925607320799087975953487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42468286188797567935875965 15925607320799087975953487)
        ·
          refine ⟨23888410981198631963930231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15925607320799087975953487 23888410981198631963930231)
          ·
            refine ⟨35832616471797947945895347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23888410981198631963930231 35832616471797947945895347)
            ·
              refine ⟨53748924707696921918843021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35832616471797947945895347 53748924707696921918843021)
              ·
                refine ⟨20155846765386345719566133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53748924707696921918843021 20155846765386345719566133)
                ·
                  refine ⟨1889610634254969911209325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20155846765386345719566133 1889610634254969911209325)
                  ·
                    refine ⟨708603987845613716703497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889610634254969911209325 708603987845613716703497)
                    ·
                      refine ⟨531452990884210287527623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708603987845613716703497 531452990884210287527623)
                      ·
                        rfl

theorem cell23_1035001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_1035001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035001 prefixEnd_1035001 := by exact prefixLift 1035001
  have htrace : WordTrace (prefixWord ++ tailWord_1035001) baseStart_1035001 baseEnd_1035001 := by
    simpa [prefixWord, tailWord_1035001, baseEnd_1035001] using wordTrace_append hprefix tailTrace_1035001
  have hstable : (prefixWord ++ tailWord_1035001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035001).length < 2 ^ (prefixWord ++ tailWord_1035001).sum := by decide
  have hdescent : baseEnd_1035001 < baseStart_1035001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035026 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1035026 : Nat := 118140960795 + 1035026 * 2 ^ 59
def prefixEnd_1035026 : Nat := 4983230072969 + 3 ^ 40 * 1035026 * 2
def baseEnd_1035026 : Nat := 531465827900572689715009

theorem tailTrace_1035026 : CollatzResearch.WordTrace tailWord_1035026 prefixEnd_1035026 531465827900572689715009 := by
  unfold tailWord_1035026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437624887071261303165233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25166999698856696808440621 9437624887071261303165233)
  ·
    refine ⟨7078218665303445977373925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9437624887071261303165233 7078218665303445977373925)
    ·
      refine ⟨1327165999744396120757611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7078218665303445977373925 1327165999744396120757611)
      ·
        refine ⟨1990748999616594181136417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327165999744396120757611 1990748999616594181136417)
        ·
          refine ⟨1493061749712445635852313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990748999616594181136417 1493061749712445635852313)
          ·
            refine ⟨1119796312284334226889235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493061749712445635852313 1119796312284334226889235)
            ·
              refine ⟨1679694468426501340333853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119796312284334226889235 1679694468426501340333853)
              ·
                refine ⟨629885425659938002625195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679694468426501340333853 629885425659938002625195)
                ·
                  refine ⟨944828138489907003937793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629885425659938002625195 944828138489907003937793)
                  ·
                    refine ⟨708621103867430252953345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944828138489907003937793 708621103867430252953345)
                    ·
                      refine ⟨531465827900572689715009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708621103867430252953345 531465827900572689715009)
                      ·
                        rfl

theorem cell23_1035026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1035026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035026 prefixEnd_1035026 := by exact prefixLift 1035026
  have htrace : WordTrace (prefixWord ++ tailWord_1035026) baseStart_1035026 baseEnd_1035026 := by
    simpa [prefixWord, tailWord_1035026, baseEnd_1035026] using wordTrace_append hprefix tailTrace_1035026
  have hstable : (prefixWord ++ tailWord_1035026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035026).length < 2 ^ (prefixWord ++ tailWord_1035026).sum := by decide
  have hdescent : baseEnd_1035026 < baseStart_1035026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035069 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1035069 : Nat := 118140960795 + 1035069 * 2 ^ 59
def prefixEnd_1035069 : Nat := 4983230072969 + 3 ^ 40 * 1035069 * 2
def baseEnd_1035069 : Nat := 531487907568716021477311

theorem tailTrace_1035069 : CollatzResearch.WordTrace tailWord_1035069 prefixEnd_1035069 531487907568716021477311 := by
  unfold tailWord_1035069
  simp only [CollatzResearch.WordTrace]
  refine ⟨37752067887129263556476261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25168045258086175704317507 37752067887129263556476261)
  ·
    refine ⟨7078512728836736916839299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37752067887129263556476261 7078512728836736916839299)
    ·
      refine ⟨10617769093255105375258949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078512728836736916839299 10617769093255105375258949)
      ·
        refine ⟨1990831704985332257861053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10617769093255105375258949 1990831704985332257861053)
        ·
          refine ⟨746561889369499596697895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1990831704985332257861053 746561889369499596697895)
          ·
            refine ⟨1119842834054249395046843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746561889369499596697895 1119842834054249395046843)
            ·
              refine ⟨1679764251081374092570265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119842834054249395046843 1679764251081374092570265)
              ·
                refine ⟨1259823188311030569427699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679764251081374092570265 1259823188311030569427699)
                ·
                  refine ⟨1889734782466545854141549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259823188311030569427699 1889734782466545854141549)
                  ·
                    refine ⟨708650543424954695303081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889734782466545854141549 708650543424954695303081)
                    ·
                      refine ⟨531487907568716021477311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708650543424954695303081 531487907568716021477311)
                      ·
                        rfl

theorem cell23_1035069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1035069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035069 prefixEnd_1035069 := by exact prefixLift 1035069
  have htrace : WordTrace (prefixWord ++ tailWord_1035069) baseStart_1035069 baseEnd_1035069 := by
    simpa [prefixWord, tailWord_1035069, baseEnd_1035069] using wordTrace_append hprefix tailTrace_1035069
  have hstable : (prefixWord ++ tailWord_1035069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035069).length < 2 ^ (prefixWord ++ tailWord_1035069).sum := by decide
  have hdescent : baseEnd_1035069 < baseStart_1035069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035091 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 5, 2]
def baseStart_1035091 : Nat := 118140960795 + 1035091 * 2 ^ 59
def prefixEnd_1035091 : Nat := 4983230072969 + 3 ^ 40 * 1035091 * 2
def baseEnd_1035091 : Nat := 531499204143114935402209

theorem tailTrace_1035091 : CollatzResearch.WordTrace tailWord_1035091 prefixEnd_1035091 531499204143114935402209 := by
  unfold tailWord_1035091
  simp only [CollatzResearch.WordTrace]
  refine ⟨37752870293049561313777127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25168580195366374209184751 37752870293049561313777127)
  ·
    refine ⟨56629305439574341970665691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37752870293049561313777127 56629305439574341970665691)
    ·
      refine ⟨84943958159361512955998537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56629305439574341970665691 84943958159361512955998537)
      ·
        refine ⟨63707968619521134716998903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84943958159361512955998537 63707968619521134716998903)
        ·
          refine ⟨95561952929281702075498355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63707968619521134716998903 95561952929281702075498355)
          ·
            refine ⟨143342929393922553113247533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95561952929281702075498355 143342929393922553113247533)
            ·
              refine ⟨53753598522720957417467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143342929393922553113247533 53753598522720957417467825)
              ·
                refine ⟨40315198892040718063100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53753598522720957417467825 40315198892040718063100869)
                ·
                  refine ⟨7559099792257634636831413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40315198892040718063100869 7559099792257634636831413)
                  ·
                    refine ⟨708665605524153247202945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7559099792257634636831413 708665605524153247202945)
                    ·
                      refine ⟨531499204143114935402209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708665605524153247202945 531499204143114935402209)
                      ·
                        rfl

theorem cell23_1035091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5, 2].length) (baseStart_1035091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035091 prefixEnd_1035091 := by exact prefixLift 1035091
  have htrace : WordTrace (prefixWord ++ tailWord_1035091) baseStart_1035091 baseEnd_1035091 := by
    simpa [prefixWord, tailWord_1035091, baseEnd_1035091] using wordTrace_append hprefix tailTrace_1035091
  have hstable : (prefixWord ++ tailWord_1035091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035091).length < 2 ^ (prefixWord ++ tailWord_1035091).sum := by decide
  have hdescent : baseEnd_1035091 < baseStart_1035091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035108 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_1035108 : Nat := 118140960795 + 1035108 * 2 ^ 59
def prefixEnd_1035108 : Nat := 4983230072969 + 3 ^ 40 * 1035108 * 2
def baseEnd_1035108 : Nat := 531507933314241368889631

theorem tailTrace_1035108 : CollatzResearch.WordTrace tailWord_1035108 prefixEnd_1035108 531507933314241368889631 := by
  unfold tailWord_1035108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876745166993986608572989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25168993555991982144763985 18876745166993986608572989)
  ·
    refine ⟨7078779437622744978214871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18876745166993986608572989 7078779437622744978214871)
    ·
      refine ⟨10618169156434117467322307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078779437622744978214871 10618169156434117467322307)
      ·
        refine ⟨15927253734651176200983461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10618169156434117467322307 15927253734651176200983461)
        ·
          refine ⟨2986360075247095537684399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15927253734651176200983461 2986360075247095537684399)
          ·
            refine ⟨4479540112870643306526599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986360075247095537684399 4479540112870643306526599)
            ·
              refine ⟨6719310169305964959789899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479540112870643306526599 6719310169305964959789899)
              ·
                refine ⟨10078965253958947439684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719310169305964959789899 10078965253958947439684849)
                ·
                  refine ⟨7559223940469210579763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10078965253958947439684849 7559223940469210579763637)
                  ·
                    refine ⟨708677244418988491852841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7559223940469210579763637 708677244418988491852841)
                    ·
                      refine ⟨531507933314241368889631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708677244418988491852841 531507933314241368889631)
                      ·
                        rfl

theorem cell23_1035108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_1035108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035108 prefixEnd_1035108 := by exact prefixLift 1035108
  have htrace : WordTrace (prefixWord ++ tailWord_1035108) baseStart_1035108 baseEnd_1035108 := by
    simpa [prefixWord, tailWord_1035108, baseEnd_1035108] using wordTrace_append hprefix tailTrace_1035108
  have hstable : (prefixWord ++ tailWord_1035108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035108).length < 2 ^ (prefixWord ++ tailWord_1035108).sum := by decide
  have hdescent : baseEnd_1035108 < baseStart_1035108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035111 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1035111 : Nat := 118140960795 + 1035111 * 2 ^ 59
def prefixEnd_1035111 : Nat := 4983230072969 + 3 ^ 40 * 1035111 * 2
def baseEnd_1035111 : Nat := 531509473756204857152117

theorem tailTrace_1035111 : CollatzResearch.WordTrace tailWord_1035111 prefixEnd_1035111 531509473756204857152117 := by
  unfold tailWord_1035111
  simp only [CollatzResearch.WordTrace]
  refine ⟨37753599752977104729505187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169066501984736486336791 37753599752977104729505187)
  ·
    refine ⟨56630399629465657094257781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37753599752977104729505187 56630399629465657094257781)
    ·
      refine ⟨5309099965262405352586667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56630399629465657094257781 5309099965262405352586667)
      ·
        refine ⟨7963649947893608028880001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309099965262405352586667 7963649947893608028880001)
        ·
          refine ⟨5972737460920206021660001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963649947893608028880001 5972737460920206021660001)
          ·
            refine ⟨4479553095690154516245001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972737460920206021660001 4479553095690154516245001)
            ·
              refine ⟨3359664821767615887183751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4479553095690154516245001 3359664821767615887183751)
              ·
                refine ⟨5039497232651423830775627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359664821767615887183751 5039497232651423830775627)
                ·
                  refine ⟨7559245848977135746163441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039497232651423830775627 7559245848977135746163441)
                  ·
                    refine ⟨5669434386732851809622581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559245848977135746163441 5669434386732851809622581)
                    ·
                      refine ⟨531509473756204857152117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5669434386732851809622581 531509473756204857152117)
                      ·
                        rfl

theorem cell23_1035111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1035111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035111 prefixEnd_1035111 := by exact prefixLift 1035111
  have htrace : WordTrace (prefixWord ++ tailWord_1035111) baseStart_1035111 baseEnd_1035111 := by
    simpa [prefixWord, tailWord_1035111, baseEnd_1035111] using wordTrace_append hprefix tailTrace_1035111
  have hstable : (prefixWord ++ tailWord_1035111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035111).length < 2 ^ (prefixWord ++ tailWord_1035111).sum := by decide
  have hdescent : baseEnd_1035111 < baseStart_1035111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035131 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 5, 4]
def baseStart_1035131 : Nat := 118140960795 + 1035131 * 2 ^ 59
def prefixEnd_1035131 : Nat := 4983230072969 + 3 ^ 40 * 1035131 * 2
def baseEnd_1035131 : Nat := 177173247789764926300675

theorem tailTrace_1035131 : CollatzResearch.WordTrace tailWord_1035131 prefixEnd_1035131 177173247789764926300675 := by
  unfold tailWord_1035131
  simp only [CollatzResearch.WordTrace]
  refine ⟨37754329212904648145233247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169552808603098763488831 37754329212904648145233247)
  ·
    refine ⟨56631493819356972217849871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37754329212904648145233247 56631493819356972217849871)
    ·
      refine ⟨84947240729035458326774807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56631493819356972217849871 84947240729035458326774807)
      ·
        refine ⟨127420861093553187490162211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84947240729035458326774807 127420861093553187490162211)
        ·
          refine ⟨191131291640329781235243317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127420861093553187490162211 191131291640329781235243317)
          ·
            refine ⟨17918558591280916990804061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191131291640329781235243317 17918558591280916990804061)
            ·
              refine ⟨6719459471730343871551523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17918558591280916990804061 6719459471730343871551523)
              ·
                refine ⟨10079189207595515807327285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719459471730343871551523 10079189207595515807327285)
                ·
                  refine ⟨944923988212079606936933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10079189207595515807327285 944923988212079606936933)
                  ·
                    refine ⟨177173247789764926300675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944923988212079606936933 177173247789764926300675)
                    ·
                      rfl

theorem cell23_1035131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 4].length) (baseStart_1035131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035131 prefixEnd_1035131 := by exact prefixLift 1035131
  have htrace : WordTrace (prefixWord ++ tailWord_1035131) baseStart_1035131 baseEnd_1035131 := by
    simpa [prefixWord, tailWord_1035131, baseEnd_1035131] using wordTrace_append hprefix tailTrace_1035131
  have hstable : (prefixWord ++ tailWord_1035131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035131).length < 2 ^ (prefixWord ++ tailWord_1035131).sum := by decide
  have hdescent : baseEnd_1035131 < baseStart_1035131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035165 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1035165 : Nat := 118140960795 + 1035165 * 2 ^ 59
def prefixEnd_1035165 : Nat := 4983230072969 + 3 ^ 40 * 1035165 * 2
def baseEnd_1035165 : Nat := 177179067237182548625623

theorem tailTrace_1035165 : CollatzResearch.WordTrace tailWord_1035165 prefixEnd_1035165 177179067237182548625623 := by
  unfold tailWord_1035165
  simp only [CollatzResearch.WordTrace]
  refine ⟨37755569294781471951970949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25170379529854314634647299 37755569294781471951970949)
  ·
    refine ⟨7079169242771525990994553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37755569294781471951970949 7079169242771525990994553)
    ·
      refine ⟨5309376932078644493245915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7079169242771525990994553 5309376932078644493245915)
      ·
        refine ⟨7964065398117966739868873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309376932078644493245915 7964065398117966739868873)
        ·
          refine ⟨5973049048588475054901655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964065398117966739868873 5973049048588475054901655)
          ·
            refine ⟨8959573572882712582352483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973049048588475054901655 8959573572882712582352483)
            ·
              refine ⟨13439360359324068873528725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8959573572882712582352483 13439360359324068873528725)
              ·
                refine ⟨629970016843315728446659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13439360359324068873528725 629970016843315728446659)
                ·
                  refine ⟨944955025264973592669989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629970016843315728446659 944955025264973592669989)
                  ·
                    refine ⟨177179067237182548625623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 944955025264973592669989 177179067237182548625623)
                    ·
                      rfl

theorem cell23_1035165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1035165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035165 prefixEnd_1035165 := by exact prefixLift 1035165
  have htrace : WordTrace (prefixWord ++ tailWord_1035165) baseStart_1035165 baseEnd_1035165 := by
    simpa [prefixWord, tailWord_1035165, baseEnd_1035165] using wordTrace_append hprefix tailTrace_1035165
  have hstable : (prefixWord ++ tailWord_1035165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035165).length < 2 ^ (prefixWord ++ tailWord_1035165).sum := by decide
  have hdescent : baseEnd_1035165 < baseStart_1035165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035191 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 3, 5]
def baseStart_1035191 : Nat := 118140960795 + 1035191 * 2 ^ 59
def prefixEnd_1035191 : Nat := 4983230072969 + 3 ^ 40 * 1035191 * 2
def baseEnd_1035191 : Nat := 177183517402854848050583

theorem tailTrace_1035191 : CollatzResearch.WordTrace tailWord_1035191 prefixEnd_1035191 177183517402854848050583 := by
  unfold tailWord_1035191
  simp only [CollatzResearch.WordTrace]
  refine ⟨37756517592687278392417427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171011728458185594944951 37756517592687278392417427)
  ·
    refine ⟨56634776389030917588626141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37756517592687278392417427 56634776389030917588626141)
    ·
      refine ⟨21238041145886594095734803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56634776389030917588626141 21238041145886594095734803)
      ·
        refine ⟨31857061718829891143602205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238041145886594095734803 31857061718829891143602205)
        ·
          refine ⟨11946398144561209178850827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31857061718829891143602205 11946398144561209178850827)
          ·
            refine ⟨17919597216841813768276241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946398144561209178850827 17919597216841813768276241)
            ·
              refine ⟨13439697912631360326207181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17919597216841813768276241 13439697912631360326207181)
              ·
                refine ⟨5039886717236760122327693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13439697912631360326207181 5039886717236760122327693)
                ·
                  refine ⟨1889957518963785045872885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5039886717236760122327693 1889957518963785045872885)
                  ·
                    refine ⟨177183517402854848050583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1889957518963785045872885 177183517402854848050583)
                    ·
                      rfl

theorem cell23_1035191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_1035191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035191 prefixEnd_1035191 := by exact prefixLift 1035191
  have htrace : WordTrace (prefixWord ++ tailWord_1035191) baseStart_1035191 baseEnd_1035191 := by
    simpa [prefixWord, tailWord_1035191, baseEnd_1035191] using wordTrace_append hprefix tailTrace_1035191
  have hstable : (prefixWord ++ tailWord_1035191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035191).length < 2 ^ (prefixWord ++ tailWord_1035191).sum := by decide
  have hdescent : baseEnd_1035191 < baseStart_1035191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035206 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1035206 : Nat := 118140960795 + 1035206 * 2 ^ 59
def prefixEnd_1035206 : Nat := 4983230072969 + 3 ^ 40 * 1035206 * 2
def baseEnd_1035206 : Nat := 531558254418381985464181

theorem tailTrace_1035206 : CollatzResearch.WordTrace tailWord_1035206 prefixEnd_1035206 531558254418381985464181 := by
  unfold tailWord_1035206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179908271488529248569171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25171376458421957302808981 1179908271488529248569171)
  ·
    refine ⟨1769862407232793872853757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179908271488529248569171 1769862407232793872853757)
    ·
      refine ⟨663698402712297702320159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1769862407232793872853757 663698402712297702320159)
      ·
        refine ⟨995547604068446553480239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663698402712297702320159 995547604068446553480239)
        ·
          refine ⟨1493321406102669830220359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995547604068446553480239 1493321406102669830220359)
          ·
            refine ⟨2239982109154004745330539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493321406102669830220359 2239982109154004745330539)
            ·
              refine ⟨3359973163731007117995809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239982109154004745330539 3359973163731007117995809)
              ·
                refine ⟨2519979872798255338496857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359973163731007117995809 2519979872798255338496857)
                ·
                  refine ⟨1889984904598691503872643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519979872798255338496857 1889984904598691503872643)
                  ·
                    refine ⟨2834977356898037255808965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1889984904598691503872643 2834977356898037255808965)
                    ·
                      refine ⟨531558254418381985464181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2834977356898037255808965 531558254418381985464181)
                      ·
                        rfl

theorem cell23_1035206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1035206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035206 prefixEnd_1035206 := by exact prefixLift 1035206
  have htrace : WordTrace (prefixWord ++ tailWord_1035206) baseStart_1035206 baseEnd_1035206 := by
    simpa [prefixWord, tailWord_1035206, baseEnd_1035206] using wordTrace_append hprefix tailTrace_1035206
  have hstable : (prefixWord ++ tailWord_1035206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035206).length < 2 ^ (prefixWord ++ tailWord_1035206).sum := by decide
  have hdescent : baseEnd_1035206 < baseStart_1035206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035215 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 2, 3, 2]
def baseStart_1035215 : Nat := 118140960795 + 1035215 * 2 ^ 59
def prefixEnd_1035215 : Nat := 4983230072969 + 3 ^ 40 * 1035215 * 2
def baseEnd_1035215 : Nat := 531562875744272450251639

theorem tailTrace_1035215 : CollatzResearch.WordTrace tailWord_1035215 prefixEnd_1035215 531562875744272450251639 := by
  unfold tailWord_1035215
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757392944600330491291099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171595296400220327527399 37757392944600330491291099)
  ·
    refine ⟨56636089416900495736936649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37757392944600330491291099 56636089416900495736936649)
    ·
      refine ⟨42477067062675371802702487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56636089416900495736936649 42477067062675371802702487)
      ·
        refine ⟨63715600594013057704053731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42477067062675371802702487 63715600594013057704053731)
        ·
          refine ⟨95573400891019586556080597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63715600594013057704053731 95573400891019586556080597)
          ·
            refine ⟨2240001583383271559908139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95573400891019586556080597 2240001583383271559908139)
            ·
              refine ⟨3360002375074907339862209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240001583383271559908139 3360002375074907339862209)
              ·
                refine ⟨2520001781306180504896657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360002375074907339862209 2520001781306180504896657)
                ·
                  refine ⟨1890001335979635378672493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2520001781306180504896657 1890001335979635378672493)
                  ·
                    refine ⟨708750500992363267002185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1890001335979635378672493 708750500992363267002185)
                    ·
                      refine ⟨531562875744272450251639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708750500992363267002185 531562875744272450251639)
                      ·
                        rfl

theorem cell23_1035215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3, 2].length) (baseStart_1035215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035215 prefixEnd_1035215 := by exact prefixLift 1035215
  have htrace : WordTrace (prefixWord ++ tailWord_1035215) baseStart_1035215 baseEnd_1035215 := by
    simpa [prefixWord, tailWord_1035215, baseEnd_1035215] using wordTrace_append hprefix tailTrace_1035215
  have hstable : (prefixWord ++ tailWord_1035215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035215).length < 2 ^ (prefixWord ++ tailWord_1035215).sum := by decide
  have hdescent : baseEnd_1035215 < baseStart_1035215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035241 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_1035241 : Nat := 118140960795 + 1035241 * 2 ^ 59
def prefixEnd_1035241 : Nat := 4983230072969 + 3 ^ 40 * 1035241 * 2
def baseEnd_1035241 : Nat := 531576226241289348526519

theorem tailTrace_1035241 : CollatzResearch.WordTrace tailWord_1035241 prefixEnd_1035241 531576226241289348526519 := by
  unfold tailWord_1035241
  simp only [CollatzResearch.WordTrace]
  refine ⟨37758341242506136931737577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25172227495004091287825051 37758341242506136931737577)
  ·
    refine ⟨28318755931879602698803183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37758341242506136931737577 28318755931879602698803183)
    ·
      refine ⟨42478133897819404048204775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28318755931879602698803183 42478133897819404048204775)
      ·
        refine ⟨63717200846729106072307163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42478133897819404048204775 63717200846729106072307163)
        ·
          refine ⟨95575801270093659108460745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63717200846729106072307163 95575801270093659108460745)
          ·
            refine ⟨71681850952570244331345559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95575801270093659108460745 71681850952570244331345559)
            ·
              refine ⟨107522776428855366497018339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71681850952570244331345559 107522776428855366497018339)
              ·
                refine ⟨161284164643283049745527509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107522776428855366497018339 161284164643283049745527509)
                ·
                  refine ⟨3780097608826946478410801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161284164643283049745527509 3780097608826946478410801)
                  ·
                    refine ⟨2835073206620209858808101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780097608826946478410801 2835073206620209858808101)
                    ·
                      refine ⟨531576226241289348526519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2835073206620209858808101 531576226241289348526519)
                      ·
                        rfl

theorem cell23_1035241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_1035241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035241 prefixEnd_1035241 := by exact prefixLift 1035241
  have htrace : WordTrace (prefixWord ++ tailWord_1035241) baseStart_1035241 baseEnd_1035241 := by
    simpa [prefixWord, tailWord_1035241, baseEnd_1035241] using wordTrace_append hprefix tailTrace_1035241
  have hstable : (prefixWord ++ tailWord_1035241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035241).length < 2 ^ (prefixWord ++ tailWord_1035241).sum := by decide
  have hdescent : baseEnd_1035241 < baseStart_1035241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035265 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1035265 : Nat := 118140960795 + 1035265 * 2 ^ 59
def prefixEnd_1035265 : Nat := 4983230072969 + 3 ^ 40 * 1035265 * 2
def baseEnd_1035265 : Nat := 531588549776997254626409

theorem tailTrace_1035265 : CollatzResearch.WordTrace tailWord_1035265 prefixEnd_1035265 531588549776997254626409 := by
  unfold tailWord_1035265
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759216594419189030611249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25172811062946126020407499 37759216594419189030611249)
  ·
    refine ⟨28319412445814391772958437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37759216594419189030611249 28319412445814391772958437)
    ·
      refine ⟨5309889833590198457429707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28319412445814391772958437 5309889833590198457429707)
      ·
        refine ⟨7964834750385297686144561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309889833590198457429707 7964834750385297686144561)
        ·
          refine ⟨5973626062788973264608421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964834750385297686144561 5973626062788973264608421)
          ·
            refine ⟨1120054886772932487114079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5973626062788973264608421 1120054886772932487114079)
            ·
              refine ⟨1680082330159398730671119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120054886772932487114079 1680082330159398730671119)
              ·
                refine ⟨2520123495239098096006679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680082330159398730671119 2520123495239098096006679)
                ·
                  refine ⟨3780185242858647144010019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520123495239098096006679 3780185242858647144010019)
                  ·
                    refine ⟨5670277864287970716015029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780185242858647144010019 5670277864287970716015029)
                    ·
                      refine ⟨531588549776997254626409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5670277864287970716015029 531588549776997254626409)
                      ·
                        rfl

theorem cell23_1035265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1035265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035265 prefixEnd_1035265 := by exact prefixLift 1035265
  have htrace : WordTrace (prefixWord ++ tailWord_1035265) baseStart_1035265 baseEnd_1035265 := by
    simpa [prefixWord, tailWord_1035265, baseEnd_1035265] using wordTrace_append hprefix tailTrace_1035265
  have hstable : (prefixWord ++ tailWord_1035265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035265).length < 2 ^ (prefixWord ++ tailWord_1035265).sum := by decide
  have hdescent : baseEnd_1035265 < baseStart_1035265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035295 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1035295 : Nat := 118140960795 + 1035295 * 2 ^ 59
def prefixEnd_1035295 : Nat := 4983230072969 + 3 ^ 40 * 1035295 * 2
def baseEnd_1035295 : Nat := 531603954196632137251271

theorem tailTrace_1035295 : CollatzResearch.WordTrace tailWord_1035295 prefixEnd_1035295 531603954196632137251271 := by
  unfold tailWord_1035295
  simp only [CollatzResearch.WordTrace]
  refine ⟨37760310784310504154203339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25173540522873669436135559 37760310784310504154203339)
  ·
    refine ⟨56640466176465756231305009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37760310784310504154203339 56640466176465756231305009)
    ·
      refine ⟨42480349632349317173478757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56640466176465756231305009 42480349632349317173478757)
      ·
        refine ⟨7965065556065496970027267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42480349632349317173478757 7965065556065496970027267)
        ·
          refine ⟨11947598334098245455040901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965065556065496970027267 11947598334098245455040901)
          ·
            refine ⟨2240174687643421022820169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11947598334098245455040901 2240174687643421022820169)
            ·
              refine ⟨1680131015732565767115127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240174687643421022820169 1680131015732565767115127)
              ·
                refine ⟨2520196523598848650672691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680131015732565767115127 2520196523598848650672691)
                ·
                  refine ⟨3780294785398272976009037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520196523598848650672691 3780294785398272976009037)
                  ·
                    refine ⟨1417610544524352366003389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780294785398272976009037 1417610544524352366003389)
                    ·
                      refine ⟨531603954196632137251271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1417610544524352366003389 531603954196632137251271)
                      ·
                        rfl

theorem cell23_1035295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1035295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035295 prefixEnd_1035295 := by exact prefixLift 1035295
  have htrace : WordTrace (prefixWord ++ tailWord_1035295) baseStart_1035295 baseEnd_1035295 := by
    simpa [prefixWord, tailWord_1035295, baseEnd_1035295] using wordTrace_append hprefix tailTrace_1035295
  have hstable : (prefixWord ++ tailWord_1035295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035295).length < 2 ^ (prefixWord ++ tailWord_1035295).sum := by decide
  have hdescent : baseEnd_1035295 < baseStart_1035295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035316 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1035316 : Nat := 118140960795 + 1035316 * 2 ^ 59
def prefixEnd_1035316 : Nat := 4983230072969 + 3 ^ 40 * 1035316 * 2
def baseEnd_1035316 : Nat := 531614737290376555088675

theorem tailTrace_1035316 : CollatzResearch.WordTrace tailWord_1035316 prefixEnd_1035316 531614737290376555088675 := by
  unfold tailWord_1035316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18880538358617212370358901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25174051144822949827145201 18880538358617212370358901)
  ·
    refine ⟨1770050471120363659721147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18880538358617212370358901 1770050471120363659721147)
    ·
      refine ⟨2655075706680545489581721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770050471120363659721147 2655075706680545489581721)
      ·
        refine ⟨1991306780010409117186291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655075706680545489581721 1991306780010409117186291)
        ·
          refine ⟨2986960170015613675779437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991306780010409117186291 2986960170015613675779437)
          ·
            refine ⟨1120110063755855128417289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2986960170015613675779437 1120110063755855128417289)
            ·
              refine ⟨840082547816891346312967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120110063755855128417289 840082547816891346312967)
              ·
                refine ⟨1260123821725337019469451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840082547816891346312967 1260123821725337019469451)
                ·
                  refine ⟨1890185732588005529204177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260123821725337019469451 1890185732588005529204177)
                  ·
                    refine ⟨1417639299441004146903133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1890185732588005529204177 1417639299441004146903133)
                    ·
                      refine ⟨531614737290376555088675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1417639299441004146903133 531614737290376555088675)
                      ·
                        rfl

theorem cell23_1035316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1035316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035316 prefixEnd_1035316 := by exact prefixLift 1035316
  have htrace : WordTrace (prefixWord ++ tailWord_1035316) baseStart_1035316 baseEnd_1035316 := by
    simpa [prefixWord, tailWord_1035316, baseEnd_1035316] using wordTrace_append hprefix tailTrace_1035316
  have hstable : (prefixWord ++ tailWord_1035316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035316).length < 2 ^ (prefixWord ++ tailWord_1035316).sum := by decide
  have hdescent : baseEnd_1035316 < baseStart_1035316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035338 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1035338 : Nat := 118140960795 + 1035338 * 2 ^ 59
def prefixEnd_1035338 : Nat := 4983230072969 + 3 ^ 40 * 1035338 * 2
def baseEnd_1035338 : Nat := 531626033864775469013573

theorem tailTrace_1035338 : CollatzResearch.WordTrace tailWord_1035338 prefixEnd_1035338 531626033864775469013573 := by
  unfold tailWord_1035338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440469780788680624504667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25174586082103148332012445 9440469780788680624504667)
  ·
    refine ⟨14160704671183020936757001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440469780788680624504667 14160704671183020936757001)
    ·
      refine ⟨10620528503387265702567751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14160704671183020936757001 10620528503387265702567751)
      ·
        refine ⟨15930792755080898553851627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620528503387265702567751 15930792755080898553851627)
        ·
          refine ⟨23896189132621347830777441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930792755080898553851627 23896189132621347830777441)
          ·
            refine ⟨17922141849466010873083081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23896189132621347830777441 17922141849466010873083081)
            ·
              refine ⟨13441606387099508154812311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17922141849466010873083081 13441606387099508154812311)
              ·
                refine ⟨20162409580649262232218467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13441606387099508154812311 20162409580649262232218467)
                ·
                  refine ⟨30243614370973893348327701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20162409580649262232218467 30243614370973893348327701)
                  ·
                    refine ⟨1417669423639401250702861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30243614370973893348327701 1417669423639401250702861)
                    ·
                      refine ⟨531626033864775469013573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1417669423639401250702861 531626033864775469013573)
                      ·
                        rfl

theorem cell23_1035338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1035338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035338 prefixEnd_1035338 := by exact prefixLift 1035338
  have htrace : WordTrace (prefixWord ++ tailWord_1035338) baseStart_1035338 baseEnd_1035338 := by
    simpa [prefixWord, tailWord_1035338, baseEnd_1035338] using wordTrace_append hprefix tailTrace_1035338
  have hstable : (prefixWord ++ tailWord_1035338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035338).length < 2 ^ (prefixWord ++ tailWord_1035338).sum := by decide
  have hdescent : baseEnd_1035338 < baseStart_1035338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035395 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 5, 2]
def baseStart_1035395 : Nat := 118140960795 + 1035395 * 2 ^ 59
def prefixEnd_1035395 : Nat := 4983230072969 + 3 ^ 40 * 1035395 * 2
def baseEnd_1035395 : Nat := 531655302262081746000811

theorem tailTrace_1035395 : CollatzResearch.WordTrace tailWord_1035395 prefixEnd_1035395 531655302262081746000811 := by
  unfold tailWord_1035395
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763958083948221232843639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175972055965480821895759 37763958083948221232843639)
  ·
    refine ⟨56645937125922331849265459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37763958083948221232843639 56645937125922331849265459)
    ·
      refine ⟨84968905688883497773898189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56645937125922331849265459 84968905688883497773898189)
      ·
        refine ⟨31863339633331311665211821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84968905688883497773898189 31863339633331311665211821)
        ·
          refine ⟨11948752362499241874454433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31863339633331311665211821 11948752362499241874454433)
          ·
            refine ⟨8961564271874431405840825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11948752362499241874454433 8961564271874431405840825)
            ·
              refine ⟨6721173203905823554380619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961564271874431405840825 6721173203905823554380619)
              ·
                refine ⟨10081759805858735331570929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721173203905823554380619 10081759805858735331570929)
                ·
                  refine ⟨7561319854394051498678197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10081759805858735331570929 7561319854394051498678197)
                  ·
                    refine ⟨708873736349442328001081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7561319854394051498678197 708873736349442328001081)
                    ·
                      refine ⟨531655302262081746000811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 708873736349442328001081 531655302262081746000811)
                      ·
                        rfl

theorem cell23_1035395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_1035395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035395 prefixEnd_1035395 := by exact prefixLift 1035395
  have htrace : WordTrace (prefixWord ++ tailWord_1035395) baseStart_1035395 baseEnd_1035395 := by
    simpa [prefixWord, tailWord_1035395, baseEnd_1035395] using wordTrace_append hprefix tailTrace_1035395
  have hstable : (prefixWord ++ tailWord_1035395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035395).length < 2 ^ (prefixWord ++ tailWord_1035395).sum := by decide
  have hdescent : baseEnd_1035395 < baseStart_1035395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035408 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_1035408 : Nat := 118140960795 + 1035408 * 2 ^ 59
def prefixEnd_1035408 : Nat := 4983230072969 + 3 ^ 40 * 1035408 * 2
def baseEnd_1035408 : Nat := 531661977510590195138251

theorem tailTrace_1035408 : CollatzResearch.WordTrace tailWord_1035408 prefixEnd_1035408 531661977510590195138251 := by
  unfold tailWord_1035408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882216116450562226533439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25176288155267416302044585 18882216116450562226533439)
  ·
    refine ⟨28323324174675843339800159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18882216116450562226533439 28323324174675843339800159)
    ·
      refine ⟨42484986262013765009700239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28323324174675843339800159 42484986262013765009700239)
      ·
        refine ⟨63727479393020647514550359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42484986262013765009700239 63727479393020647514550359)
        ·
          refine ⟨95591219089530971271825539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63727479393020647514550359 95591219089530971271825539)
          ·
            refine ⟨143386828634296456907738309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95591219089530971271825539 143386828634296456907738309)
            ·
              refine ⟨26885030368930585670200933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143386828634296456907738309 26885030368930585670200933)
              ·
                refine ⟨5040943194174484813162675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26885030368930585670200933 5040943194174484813162675)
                ·
                  refine ⟨7561414791261727219744013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040943194174484813162675 7561414791261727219744013)
                  ·
                    refine ⟨2835530546723147707404005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7561414791261727219744013 2835530546723147707404005)
                    ·
                      refine ⟨531661977510590195138251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2835530546723147707404005 531661977510590195138251)
                      ·
                        rfl

theorem cell23_1035408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_1035408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035408 prefixEnd_1035408 := by exact prefixLift 1035408
  have htrace : WordTrace (prefixWord ++ tailWord_1035408) baseStart_1035408 baseEnd_1035408 := by
    simpa [prefixWord, tailWord_1035408, baseEnd_1035408] using wordTrace_append hprefix tailTrace_1035408
  have hstable : (prefixWord ++ tailWord_1035408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035408).length < 2 ^ (prefixWord ++ tailWord_1035408).sum := by decide
  have hdescent : baseEnd_1035408 < baseStart_1035408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035422 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1035422 : Nat := 118140960795 + 1035422 * 2 ^ 59
def prefixEnd_1035422 : Nat := 4983230072969 + 3 ^ 40 * 1035422 * 2
def baseEnd_1035422 : Nat := 177223055413251046787729

theorem tailTrace_1035422 : CollatzResearch.WordTrace tailWord_1035422 prefixEnd_1035422 177223055413251046787729 := by
  unfold tailWord_1035422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720617856856300605509565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25176628569900269896051013 4720617856856300605509565)
  ·
    refine ⟨1770231696321112727066087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4720617856856300605509565 1770231696321112727066087)
    ·
      refine ⟨2655347544481669090599131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770231696321112727066087 2655347544481669090599131)
      ·
        refine ⟨3983021316722503635898697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655347544481669090599131 3983021316722503635898697)
        ·
          refine ⟨2987265987541877726924023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983021316722503635898697 2987265987541877726924023)
          ·
            refine ⟨4480898981312816590386035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987265987541877726924023 4480898981312816590386035)
            ·
              refine ⟨6721348471969224885579053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480898981312816590386035 6721348471969224885579053)
              ·
                refine ⟨2520505676988459332092145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6721348471969224885579053 2520505676988459332092145)
                ·
                  refine ⟨1890379257741344499069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2520505676988459332092145 1890379257741344499069109)
                  ·
                    refine ⟨177223055413251046787729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1890379257741344499069109 177223055413251046787729)
                    ·
                      rfl

theorem cell23_1035422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1035422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035422 prefixEnd_1035422 := by exact prefixLift 1035422
  have htrace : WordTrace (prefixWord ++ tailWord_1035422) baseStart_1035422 baseEnd_1035422 := by
    simpa [prefixWord, tailWord_1035422, baseEnd_1035422] using wordTrace_append hprefix tailTrace_1035422
  have hstable : (prefixWord ++ tailWord_1035422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035422).length < 2 ^ (prefixWord ++ tailWord_1035422).sum := by decide
  have hdescent : baseEnd_1035422 < baseStart_1035422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035476 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1035476 : Nat := 118140960795 + 1035476 * 2 ^ 59
def prefixEnd_1035476 : Nat := 4983230072969 + 3 ^ 40 * 1035476 * 2
def baseEnd_1035476 : Nat := 531696894195095929087939

theorem tailTrace_1035476 : CollatzResearch.WordTrace tailWord_1035476 prefixEnd_1035476 531696894195095929087939 := by
  unfold tailWord_1035476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883456198327386033271141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25177941597769848044361521 18883456198327386033271141)
  ·
    refine ⟨3540648037186384881238339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18883456198327386033271141 3540648037186384881238339)
    ·
      refine ⟨5310972055779577321857509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540648037186384881238339 5310972055779577321857509)
      ·
        refine ⟨995807260458670747848283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5310972055779577321857509 995807260458670747848283)
        ·
          refine ⟨1493710890688006121772425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995807260458670747848283 1493710890688006121772425)
          ·
            refine ⟨1120283168016004591329319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493710890688006121772425 1120283168016004591329319)
            ·
              refine ⟨1680424752024006886993979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120283168016004591329319 1680424752024006886993979)
              ·
                refine ⟨2520637128036010330490969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680424752024006886993979 2520637128036010330490969)
                ·
                  refine ⟨1890477846027007747868227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2520637128036010330490969 1890477846027007747868227)
                  ·
                    refine ⟨2835716769040511621802341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890477846027007747868227 2835716769040511621802341)
                    ·
                      refine ⟨531696894195095929087939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2835716769040511621802341 531696894195095929087939)
                      ·
                        rfl

theorem cell23_1035476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1035476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035476 prefixEnd_1035476 := by exact prefixLift 1035476
  have htrace : WordTrace (prefixWord ++ tailWord_1035476) baseStart_1035476 baseEnd_1035476 := by
    simpa [prefixWord, tailWord_1035476, baseEnd_1035476] using wordTrace_append hprefix tailTrace_1035476
  have hstable : (prefixWord ++ tailWord_1035476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035476).length < 2 ^ (prefixWord ++ tailWord_1035476).sum := by decide
  have hdescent : baseEnd_1035476 < baseStart_1035476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035532 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_1035532 : Nat := 118140960795 + 1035532 * 2 ^ 59
def prefixEnd_1035532 : Nat := 4983230072969 + 3 ^ 40 * 1035532 * 2
def baseEnd_1035532 : Nat := 531725649111747709987681

theorem tailTrace_1035532 : CollatzResearch.WordTrace tailWord_1035532 prefixEnd_1035532 531725649111747709987681 := by
  unfold tailWord_1035532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884477442225946815290425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25179303256301262420387233 18884477442225946815290425)
  ·
    refine ⟨14163358081669460111467819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18884477442225946815290425 14163358081669460111467819)
    ·
      refine ⟨21245037122504190167201729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14163358081669460111467819 21245037122504190167201729)
      ·
        refine ⟨15933777841878142625401297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21245037122504190167201729 15933777841878142625401297)
        ·
          refine ⟨11950333381408606969050973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15933777841878142625401297 11950333381408606969050973)
          ·
            refine ⟨4481375018028227613394115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11950333381408606969050973 4481375018028227613394115)
            ·
              refine ⟨6722062527042341420091173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481375018028227613394115 6722062527042341420091173)
              ·
                refine ⟨1260386723820439016267095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6722062527042341420091173 1260386723820439016267095)
                ·
                  refine ⟨1890580085730658524400643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260386723820439016267095 1890580085730658524400643)
                  ·
                    refine ⟨2835870128595987786600965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890580085730658524400643 2835870128595987786600965)
                    ·
                      refine ⟨531725649111747709987681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2835870128595987786600965 531725649111747709987681)
                      ·
                        rfl

theorem cell23_1035532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_1035532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035532 prefixEnd_1035532 := by exact prefixLift 1035532
  have htrace : WordTrace (prefixWord ++ tailWord_1035532) baseStart_1035532 baseEnd_1035532 := by
    simpa [prefixWord, tailWord_1035532, baseEnd_1035532] using wordTrace_append hprefix tailTrace_1035532
  have hstable : (prefixWord ++ tailWord_1035532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035532).length < 2 ^ (prefixWord ++ tailWord_1035532).sum := by decide
  have hdescent : baseEnd_1035532 < baseStart_1035532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035549 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1035549 : Nat := 118140960795 + 1035549 * 2 ^ 59
def prefixEnd_1035549 : Nat := 4983230072969 + 3 ^ 40 * 1035549 * 2
def baseEnd_1035549 : Nat := 531734378282874143475103

theorem tailTrace_1035549 : CollatzResearch.WordTrace tailWord_1035549 prefixEnd_1035549 531734378282874143475103 := by
  unfold tailWord_1035549
  simp only [CollatzResearch.WordTrace]
  refine ⟨37769574925390305533949701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25179716616926870355966467 37769574925390305533949701)
  ·
    refine ⟨7081795298510682287615569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37769574925390305533949701 7081795298510682287615569)
    ·
      refine ⟨5311346473883011715711677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7081795298510682287615569 5311346473883011715711677)
      ·
        refine ⟨1991754927706129393391879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5311346473883011715711677 1991754927706129393391879)
        ·
          refine ⟨2987632391559194090087819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991754927706129393391879 2987632391559194090087819)
          ·
            refine ⟨4481448587338791135131729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987632391559194090087819 4481448587338791135131729)
            ·
              refine ⟨3361086440504093351348797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481448587338791135131729 3361086440504093351348797)
              ·
                refine ⟨1260407415189035006755799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361086440504093351348797 1260407415189035006755799)
                ·
                  refine ⟨1890611122783552510133699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260407415189035006755799 1890611122783552510133699)
                  ·
                    refine ⟨2835916684175328765200549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890611122783552510133699 2835916684175328765200549)
                    ·
                      refine ⟨531734378282874143475103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2835916684175328765200549 531734378282874143475103)
                      ·
                        rfl

theorem cell23_1035549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1035549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035549 prefixEnd_1035549 := by exact prefixLift 1035549
  have htrace : WordTrace (prefixWord ++ tailWord_1035549) baseStart_1035549 baseEnd_1035549 := by
    simpa [prefixWord, tailWord_1035549, baseEnd_1035549] using wordTrace_append hprefix tailTrace_1035549
  have hstable : (prefixWord ++ tailWord_1035549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035549).length < 2 ^ (prefixWord ++ tailWord_1035549).sum := by decide
  have hdescent : baseEnd_1035549 < baseStart_1035549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035555 : List Nat := [1, 1, 1, 4, 2, 5, 9]
def baseStart_1035555 : Nat := 118140960795 + 1035555 * 2 ^ 59
def prefixEnd_1035555 : Nat := 4983230072969 + 3 ^ 40 * 1035555 * 2
def baseEnd_1035555 : Nat := 6564659989713594074075

theorem tailTrace_1035555 : CollatzResearch.WordTrace tailWord_1035555 prefixEnd_1035555 6564659989713594074075 := by
  unfold tailWord_1035555
  simp only [CollatzResearch.WordTrace]
  refine ⟨37769793763368568558668119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25179862508912379039112079 37769793763368568558668119)
  ·
    refine ⟨56654690645052852838002179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37769793763368568558668119 56654690645052852838002179)
    ·
      refine ⟨84982035967579279257003269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56654690645052852838002179 84982035967579279257003269)
      ·
        refine ⟨15934131743921114860688113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84982035967579279257003269 15934131743921114860688113)
        ·
          refine ⟨11950598807940836145516085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15934131743921114860688113 11950598807940836145516085)
          ·
            refine ⟨1120368638244453388642133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11950598807940836145516085 1120368638244453388642133)
            ·
              refine ⟨6564659989713594074075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1120368638244453388642133 6564659989713594074075)
              ·
                rfl

theorem cell23_1035555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 9].length) (baseStart_1035555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035555 prefixEnd_1035555 := by exact prefixLift 1035555
  have htrace : WordTrace (prefixWord ++ tailWord_1035555) baseStart_1035555 baseEnd_1035555 := by
    simpa [prefixWord, tailWord_1035555, baseEnd_1035555] using wordTrace_append hprefix tailTrace_1035555
  have hstable : (prefixWord ++ tailWord_1035555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035555).length < 2 ^ (prefixWord ++ tailWord_1035555).sum := by decide
  have hdescent : baseEnd_1035555 < baseStart_1035555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035562 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1035562 : Nat := 118140960795 + 1035562 * 2 ^ 59
def prefixEnd_1035562 : Nat := 4983230072969 + 3 ^ 40 * 1035562 * 2
def baseEnd_1035562 : Nat := 531741053531382592612543

theorem tailTrace_1035562 : CollatzResearch.WordTrace tailWord_1035562 prefixEnd_1035562 531741053531382592612543 := by
  unfold tailWord_1035562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442512268585802188543235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25180032716228805836115293 9442512268585802188543235)
  ·
    refine ⟨14163768402878703282814853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9442512268585802188543235 14163768402878703282814853)
    ·
      refine ⟨2655706575539756865527785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14163768402878703282814853 2655706575539756865527785)
      ·
        refine ⟨1991779931654817649145839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655706575539756865527785 1991779931654817649145839)
        ·
          refine ⟨2987669897482226473718759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991779931654817649145839 2987669897482226473718759)
          ·
            refine ⟨4481504846223339710578139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987669897482226473718759 4481504846223339710578139)
            ·
              refine ⟨6722257269335009565867209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481504846223339710578139 6722257269335009565867209)
              ·
                refine ⟨5041692952001257174400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722257269335009565867209 5041692952001257174400407)
                ·
                  refine ⟨7562539428001885761600611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041692952001257174400407 7562539428001885761600611)
                  ·
                    refine ⟨11343809142002828642400917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562539428001885761600611 11343809142002828642400917)
                    ·
                      refine ⟨531741053531382592612543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11343809142002828642400917 531741053531382592612543)
                      ·
                        rfl

theorem cell23_1035562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1035562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035562 prefixEnd_1035562 := by exact prefixLift 1035562
  have htrace : WordTrace (prefixWord ++ tailWord_1035562) baseStart_1035562 baseEnd_1035562 := by
    simpa [prefixWord, tailWord_1035562, baseEnd_1035562] using wordTrace_append hprefix tailTrace_1035562
  have hstable : (prefixWord ++ tailWord_1035562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035562).length < 2 ^ (prefixWord ++ tailWord_1035562).sum := by decide
  have hdescent : baseEnd_1035562 < baseStart_1035562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035572 : List Nat := [2, 5, 1, 1, 1, 1, 4, 8]
def baseStart_1035572 : Nat := 118140960795 + 1035572 * 2 ^ 59
def prefixEnd_1035572 : Nat := 4983230072969 + 3 ^ 40 * 1035572 * 2
def baseEnd_1035572 : Nat := 19694303271775094573611

theorem tailTrace_1035572 : CollatzResearch.WordTrace tailWord_1035572 prefixEnd_1035572 19694303271775094573611 := by
  unfold tailWord_1035572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885206902153490231018485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25180275869537986974691313 18885206902153490231018485)
  ·
    refine ⟨1770488147076889709157983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18885206902153490231018485 1770488147076889709157983)
    ·
      refine ⟨2655732220615334563736975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770488147076889709157983 2655732220615334563736975)
      ·
        refine ⟨3983598330923001845605463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655732220615334563736975 3983598330923001845605463)
        ·
          refine ⟨5975397496384502768408195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983598330923001845605463 5975397496384502768408195)
          ·
            refine ⟨8963096244576754152612293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975397496384502768408195 8963096244576754152612293)
            ·
              refine ⟨1680580545858141403614805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8963096244576754152612293 1680580545858141403614805)
              ·
                refine ⟨19694303271775094573611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1680580545858141403614805 19694303271775094573611)
                ·
                  rfl

theorem cell23_1035572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 8].length) (baseStart_1035572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035572 prefixEnd_1035572 := by exact prefixLift 1035572
  have htrace : WordTrace (prefixWord ++ tailWord_1035572) baseStart_1035572 baseEnd_1035572 := by
    simpa [prefixWord, tailWord_1035572, baseEnd_1035572] using wordTrace_append hprefix tailTrace_1035572
  have hstable : (prefixWord ++ tailWord_1035572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035572).length < 2 ^ (prefixWord ++ tailWord_1035572).sum := by decide
  have hdescent : baseEnd_1035572 < baseStart_1035572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035606 : List Nat := [5, 2, 3, 1, 1, 11]
def baseStart_1035606 : Nat := 118140960795 + 1035606 * 2 ^ 59
def prefixEnd_1035606 : Nat := 4983230072969 + 3 ^ 40 * 1035606 * 2
def baseEnd_1035606 : Nat := 2188327764115968808487

theorem tailTrace_1035606 : CollatzResearch.WordTrace tailWord_1035606 prefixEnd_1035606 2188327764115968808487 := by
  unfold tailWord_1035606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360728367886487766798417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25181102590789202845849781 2360728367886487766798417)
  ·
    refine ⟨1770546275914865825098813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2360728367886487766798417 1770546275914865825098813)
    ·
      refine ⟨663954853468074684412055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1770546275914865825098813 663954853468074684412055)
      ·
        refine ⟨995932280202112026618083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663954853468074684412055 995932280202112026618083)
        ·
          refine ⟨1493898420303168039927125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995932280202112026618083 1493898420303168039927125)
          ·
            refine ⟨2188327764115968808487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1493898420303168039927125 2188327764115968808487)
            ·
              rfl

theorem cell23_1035606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 11].length) (baseStart_1035606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035606 prefixEnd_1035606 := by exact prefixLift 1035606
  have htrace : WordTrace (prefixWord ++ tailWord_1035606) baseStart_1035606 baseEnd_1035606 := by
    simpa [prefixWord, tailWord_1035606, baseEnd_1035606] using wordTrace_append hprefix tailTrace_1035606
  have hstable : (prefixWord ++ tailWord_1035606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035606).length < 2 ^ (prefixWord ++ tailWord_1035606).sum := by decide
  have hdescent : baseEnd_1035606 < baseStart_1035606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035609 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 1, 3, 2]
def baseStart_1035609 : Nat := 118140960795 + 1035609 * 2 ^ 59
def prefixEnd_1035609 : Nat := 4983230072969 + 3 ^ 40 * 1035609 * 2
def baseEnd_1035609 : Nat := 531765187122143908724827

theorem tailTrace_1035609 : CollatzResearch.WordTrace tailWord_1035609 prefixEnd_1035609 531765187122143908724827 := by
  unfold tailWord_1035609
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771763305172935781133881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181175536781957187422587 37771763305172935781133881)
  ·
    refine ⟨28328822478879701835850411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37771763305172935781133881 28328822478879701835850411)
    ·
      refine ⟨42493233718319552753775617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28328822478879701835850411 42493233718319552753775617)
      ·
        refine ⟨31869925288739664565331713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42493233718319552753775617 31869925288739664565331713)
        ·
          refine ⟨23902443966554748423998785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31869925288739664565331713 23902443966554748423998785)
          ·
            refine ⟨17926832974916061317999089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23902443966554748423998785 17926832974916061317999089)
            ·
              refine ⟨13445124731187045988499317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17926832974916061317999089 13445124731187045988499317)
              ·
                refine ⟨1260480443548785561421811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13445124731187045988499317 1260480443548785561421811)
                ·
                  refine ⟨1890720665323178342132717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260480443548785561421811 1890720665323178342132717)
                  ·
                    refine ⟨709020249496191878299769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1890720665323178342132717 709020249496191878299769)
                    ·
                      refine ⟨531765187122143908724827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709020249496191878299769 531765187122143908724827)
                      ·
                        rfl

theorem cell23_1035609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_1035609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035609 prefixEnd_1035609 := by exact prefixLift 1035609
  have htrace : WordTrace (prefixWord ++ tailWord_1035609) baseStart_1035609 baseEnd_1035609 := by
    simpa [prefixWord, tailWord_1035609, baseEnd_1035609] using wordTrace_append hprefix tailTrace_1035609
  have hstable : (prefixWord ++ tailWord_1035609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035609).length < 2 ^ (prefixWord ++ tailWord_1035609).sum := by decide
  have hdescent : baseEnd_1035609 < baseStart_1035609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035615 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 6]
def baseStart_1035615 : Nat := 118140960795 + 1035615 * 2 ^ 59
def prefixEnd_1035615 : Nat := 4983230072969 + 3 ^ 40 * 1035615 * 2
def baseEnd_1035615 : Nat := 177256089335356961749933

theorem tailTrace_1035615 : CollatzResearch.WordTrace tailWord_1035615 prefixEnd_1035615 177256089335356961749933 := by
  unfold tailWord_1035615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771982143151198805852299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181321428767465870568199 37771982143151198805852299)
  ·
    refine ⟨56657973214726798208778449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37771982143151198805852299 56657973214726798208778449)
    ·
      refine ⟨42493479911045098656583837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56657973214726798208778449 42493479911045098656583837)
      ·
        refine ⟨15935054966641911996218939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42493479911045098656583837 15935054966641911996218939)
        ·
          refine ⟨23902582449962867994328409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15935054966641911996218939 23902582449962867994328409)
          ·
            refine ⟨17926936837472150995746307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23902582449962867994328409 17926936837472150995746307)
            ·
              refine ⟨26890405256208226493619461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926936837472150995746307 26890405256208226493619461)
              ·
                refine ⟨5041950985539042467553649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26890405256208226493619461 5041950985539042467553649)
                ·
                  refine ⟨3781463239154281850665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041950985539042467553649 3781463239154281850665237)
                  ·
                    refine ⟨177256089335356961749933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3781463239154281850665237 177256089335356961749933)
                    ·
                      rfl

theorem cell23_1035615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_1035615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035615 prefixEnd_1035615 := by exact prefixLift 1035615
  have htrace : WordTrace (prefixWord ++ tailWord_1035615) baseStart_1035615 baseEnd_1035615 := by
    simpa [prefixWord, tailWord_1035615, baseEnd_1035615] using wordTrace_append hprefix tailTrace_1035615
  have hstable : (prefixWord ++ tailWord_1035615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035615).length < 2 ^ (prefixWord ++ tailWord_1035615).sum := by decide
  have hdescent : baseEnd_1035615 < baseStart_1035615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035616 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_1035616 : Nat := 118140960795 + 1035616 * 2 ^ 59
def prefixEnd_1035616 : Nat := 4983230072969 + 3 ^ 40 * 1035616 * 2
def baseEnd_1035616 : Nat := 531768781486725381337295

theorem tailTrace_1035616 : CollatzResearch.WordTrace tailWord_1035616 prefixEnd_1035616 531768781486725381337295 := by
  unfold tailWord_1035616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886009308073787988319351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25181345744098383984425801 18886009308073787988319351)
  ·
    refine ⟨28329013962110681982479027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18886009308073787988319351 28329013962110681982479027)
    ·
      refine ⟨42493520943166022973718541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28329013962110681982479027 42493520943166022973718541)
      ·
        refine ⟨15935070353687258615144453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42493520943166022973718541 15935070353687258615144453)
        ·
          refine ⟨2987825691316360990339585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15935070353687258615144453 2987825691316360990339585)
          ·
            refine ⟨2240869268487270742754689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987825691316360990339585 2240869268487270742754689)
            ·
              refine ⟨1680651951365453057066017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240869268487270742754689 1680651951365453057066017)
              ·
                refine ⟨1260488963524089792799513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680651951365453057066017 1260488963524089792799513)
                ·
                  refine ⟨945366722643067344599635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260488963524089792799513 945366722643067344599635)
                  ·
                    refine ⟨1418050083964601016899453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945366722643067344599635 1418050083964601016899453)
                    ·
                      refine ⟨531768781486725381337295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418050083964601016899453 531768781486725381337295)
                      ·
                        rfl

theorem cell23_1035616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_1035616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035616 prefixEnd_1035616 := by exact prefixLift 1035616
  have htrace : WordTrace (prefixWord ++ tailWord_1035616) baseStart_1035616 baseEnd_1035616 := by
    simpa [prefixWord, tailWord_1035616, baseEnd_1035616] using wordTrace_append hprefix tailTrace_1035616
  have hstable : (prefixWord ++ tailWord_1035616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035616).length < 2 ^ (prefixWord ++ tailWord_1035616).sum := by decide
  have hdescent : baseEnd_1035616 < baseStart_1035616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035625 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_1035625 : Nat := 118140960795 + 1035625 * 2 ^ 59
def prefixEnd_1035625 : Nat := 4983230072969 + 3 ^ 40 * 1035625 * 2
def baseEnd_1035625 : Nat := 531773402812615846124753

theorem tailTrace_1035625 : CollatzResearch.WordTrace tailWord_1035625 prefixEnd_1035625 531773402812615846124753 := by
  unfold tailWord_1035625
  simp only [CollatzResearch.WordTrace]
  refine ⟨37772346873114970513716329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181564582076647009144219 37772346873114970513716329)
  ·
    refine ⟨28329260154836227885287247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37772346873114970513716329 28329260154836227885287247)
    ·
      refine ⟨42493890232254341827930871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28329260154836227885287247 42493890232254341827930871)
      ·
        refine ⟨63740835348381512741896307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42493890232254341827930871 63740835348381512741896307)
        ·
          refine ⟨95611253022572269112844461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63740835348381512741896307 95611253022572269112844461)
          ·
            refine ⟨35854219883464600917316673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95611253022572269112844461 35854219883464600917316673)
            ·
              refine ⟨26890664912598450687987505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35854219883464600917316673 26890664912598450687987505)
              ·
                refine ⟨20167998684448838015990629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26890664912598450687987505 20167998684448838015990629)
                ·
                  refine ⟨3781499753334157127998243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20167998684448838015990629 3781499753334157127998243)
                  ·
                    refine ⟨5672249630001235691997365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781499753334157127998243 5672249630001235691997365)
                    ·
                      refine ⟨531773402812615846124753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5672249630001235691997365 531773402812615846124753)
                      ·
                        rfl

theorem cell23_1035625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_1035625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035625 prefixEnd_1035625 := by exact prefixLift 1035625
  have htrace : WordTrace (prefixWord ++ tailWord_1035625) baseStart_1035625 baseEnd_1035625 := by
    simpa [prefixWord, tailWord_1035625, baseEnd_1035625] using wordTrace_append hprefix tailTrace_1035625
  have hstable : (prefixWord ++ tailWord_1035625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035625).length < 2 ^ (prefixWord ++ tailWord_1035625).sum := by decide
  have hdescent : baseEnd_1035625 < baseStart_1035625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035639 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_1035639 : Nat := 118140960795 + 1035639 * 2 ^ 59
def prefixEnd_1035639 : Nat := 4983230072969 + 3 ^ 40 * 1035639 * 2
def baseEnd_1035639 : Nat := 531780591541778791349689

theorem tailTrace_1035639 : CollatzResearch.WordTrace tailWord_1035639 prefixEnd_1035639 531780591541778791349689 := by
  unfold tailWord_1035639
  simp only [CollatzResearch.WordTrace]
  refine ⟨37772857495064250904725971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181904996709500603150647 37772857495064250904725971)
  ·
    refine ⟨56659286242596376357088957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37772857495064250904725971 56659286242596376357088957)
    ·
      refine ⟨21247232340973641133908359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56659286242596376357088957 21247232340973641133908359)
      ·
        refine ⟨31870848511460461700862539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21247232340973641133908359 31870848511460461700862539)
        ·
          refine ⟨47806272767190692551293809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31870848511460461700862539 47806272767190692551293809)
          ·
            refine ⟨35854704575393019413470357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47806272767190692551293809 35854704575393019413470357)
            ·
              refine ⟨1680689276971547785006423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35854704575393019413470357 1680689276971547785006423)
              ·
                refine ⟨2521033915457321677509635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680689276971547785006423 2521033915457321677509635)
                ·
                  refine ⟨3781550873185982516264453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521033915457321677509635 3781550873185982516264453)
                  ·
                    refine ⟨709040788722371721799585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781550873185982516264453 709040788722371721799585)
                    ·
                      refine ⟨531780591541778791349689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709040788722371721799585 531780591541778791349689)
                      ·
                        rfl

theorem cell23_1035639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_1035639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035639 prefixEnd_1035639 := by exact prefixLift 1035639
  have htrace : WordTrace (prefixWord ++ tailWord_1035639) baseStart_1035639 baseEnd_1035639 := by
    simpa [prefixWord, tailWord_1035639, baseEnd_1035639] using wordTrace_append hprefix tailTrace_1035639
  have hstable : (prefixWord ++ tailWord_1035639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035639).length < 2 ^ (prefixWord ++ tailWord_1035639).sum := by decide
  have hdescent : baseEnd_1035639 < baseStart_1035639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035673 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 2, 2, 2]
def baseStart_1035673 : Nat := 118140960795 + 1035673 * 2 ^ 59
def prefixEnd_1035673 : Nat := 4983230072969 + 3 ^ 40 * 1035673 * 2
def baseEnd_1035673 : Nat := 531798049884031658324533

theorem tailTrace_1035673 : CollatzResearch.WordTrace tailWord_1035673 prefixEnd_1035673 531798049884031658324533 := by
  unfold tailWord_1035673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774097576941074711463673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25182731717960716474309115 37774097576941074711463673)
  ·
    refine ⟨28330573182705806033597755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37774097576941074711463673 28330573182705806033597755)
    ·
      refine ⟨42495859774058709050396633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330573182705806033597755 42495859774058709050396633)
      ·
        refine ⟨31871894830544031787797475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42495859774058709050396633 31871894830544031787797475)
        ·
          refine ⟨47807842245816047681696213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31871894830544031787797475 47807842245816047681696213)
          ·
            refine ⟨1120496302636313617539755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47807842245816047681696213 1120496302636313617539755)
            ·
              refine ⟨1680744453954470426309633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120496302636313617539755 1680744453954470426309633)
              ·
                refine ⟨1260558340465852819732225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680744453954470426309633 1260558340465852819732225)
                ·
                  refine ⟨945418755349389614799169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260558340465852819732225 945418755349389614799169)
                  ·
                    refine ⟨709064066512042211099377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 945418755349389614799169 709064066512042211099377)
                    ·
                      refine ⟨531798049884031658324533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709064066512042211099377 531798049884031658324533)
                      ·
                        rfl

theorem cell23_1035673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_1035673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035673 prefixEnd_1035673 := by exact prefixLift 1035673
  have htrace : WordTrace (prefixWord ++ tailWord_1035673) baseStart_1035673 baseEnd_1035673 := by
    simpa [prefixWord, tailWord_1035673, baseEnd_1035673] using wordTrace_append hprefix tailTrace_1035673
  have hstable : (prefixWord ++ tailWord_1035673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035673).length < 2 ^ (prefixWord ++ tailWord_1035673).sum := by decide
  have hdescent : baseEnd_1035673 < baseStart_1035673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035679 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 5]
def baseStart_1035679 : Nat := 118140960795 + 1035679 * 2 ^ 59
def prefixEnd_1035679 : Nat := 4983230072969 + 3 ^ 40 * 1035679 * 2
def baseEnd_1035679 : Nat := 59089014529773181649945

theorem tailTrace_1035679 : CollatzResearch.WordTrace tailWord_1035679 prefixEnd_1035679 59089014529773181649945 := by
  unfold tailWord_1035679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774316414919337736182091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25182877609946225157454727 37774316414919337736182091)
  ·
    refine ⟨56661474622379006604273137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37774316414919337736182091 56661474622379006604273137)
    ·
      refine ⟨42496105966784254953204853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56661474622379006604273137 42496105966784254953204853)
      ·
        refine ⟨3984009934386023901862955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42496105966784254953204853 3984009934386023901862955)
        ·
          refine ⟨5976014901579035852794433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984009934386023901862955 5976014901579035852794433)
          ·
            refine ⟨4482011176184276889595825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976014901579035852794433 4482011176184276889595825)
            ·
              refine ⟨3361508382138207667196869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482011176184276889595825 3361508382138207667196869)
              ·
                refine ⟨630282821650913937599413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3361508382138207667196869 630282821650913937599413)
                ·
                  refine ⟨59089014529773181649945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 630282821650913937599413 59089014529773181649945)
                  ·
                    rfl

theorem cell23_1035679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 5].length) (baseStart_1035679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035679 prefixEnd_1035679 := by exact prefixLift 1035679
  have htrace : WordTrace (prefixWord ++ tailWord_1035679) baseStart_1035679 baseEnd_1035679 := by
    simpa [prefixWord, tailWord_1035679, baseEnd_1035679] using wordTrace_append hprefix tailTrace_1035679
  have hstable : (prefixWord ++ tailWord_1035679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035679).length < 2 ^ (prefixWord ++ tailWord_1035679).sum := by decide
  have hdescent : baseEnd_1035679 < baseStart_1035679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035712 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1035712 : Nat := 118140960795 + 1035712 * 2 ^ 59
def prefixEnd_1035712 : Nat := 4983230072969 + 3 ^ 40 * 1035712 * 2
def baseEnd_1035712 : Nat := 531818075629557005736853

theorem tailTrace_1035712 : CollatzResearch.WordTrace tailWord_1035712 prefixEnd_1035712 531818075629557005736853 := by
  unfold tailWord_1035712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887760011899892186066695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25183680015866522914755593 18887760011899892186066695)
  ·
    refine ⟨28331640017849838279100043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887760011899892186066695 28331640017849838279100043)
    ·
      refine ⟨42497460026774757418650065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28331640017849838279100043 42497460026774757418650065)
      ·
        refine ⟨31873095020081068063987549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42497460026774757418650065 31873095020081068063987549)
        ·
          refine ⟨11952410632530400523995331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31873095020081068063987549 11952410632530400523995331)
          ·
            refine ⟨17928615948795600785992997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952410632530400523995331 17928615948795600785992997)
            ·
              refine ⟨3361615490399175147373687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17928615948795600785992997 3361615490399175147373687)
              ·
                refine ⟨5042423235598762721060531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361615490399175147373687 5042423235598762721060531)
                ·
                  refine ⟨7563634853398144081590797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042423235598762721060531 7563634853398144081590797)
                  ·
                    refine ⟨2836363070024304030596549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7563634853398144081590797 2836363070024304030596549)
                    ·
                      refine ⟨531818075629557005736853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2836363070024304030596549 531818075629557005736853)
                      ·
                        rfl

theorem cell23_1035712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1035712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035712 prefixEnd_1035712 := by exact prefixLift 1035712
  have htrace : WordTrace (prefixWord ++ tailWord_1035712) baseStart_1035712 baseEnd_1035712 := by
    simpa [prefixWord, tailWord_1035712, baseEnd_1035712] using wordTrace_append hprefix tailTrace_1035712
  have hstable : (prefixWord ++ tailWord_1035712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035712).length < 2 ^ (prefixWord ++ tailWord_1035712).sum := by decide
  have hdescent : baseEnd_1035712 < baseStart_1035712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035766 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1035766 : Nat := 118140960795 + 1035766 * 2 ^ 59
def prefixEnd_1035766 : Nat := 4983230072969 + 3 ^ 40 * 1035766 * 2
def baseEnd_1035766 : Nat := 531845803584899794461605

theorem tailTrace_1035766 : CollatzResearch.WordTrace tailWord_1035766 prefixEnd_1035766 531845803584899794461605 := by
  unfold tailWord_1035766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361093097850259474662447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25184993043736101063066101 2361093097850259474662447)
  ·
    refine ⟨3541639646775389211993671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361093097850259474662447 3541639646775389211993671)
    ·
      refine ⟨5312459470163083817990507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541639646775389211993671 5312459470163083817990507)
      ·
        refine ⟨7968689205244625726985761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312459470163083817990507 7968689205244625726985761)
        ·
          refine ⟨5976516903933469295239321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7968689205244625726985761 5976516903933469295239321)
          ·
            refine ⟨4482387677950101971429491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976516903933469295239321 4482387677950101971429491)
            ·
              refine ⟨6723581516925152957144237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482387677950101971429491 6723581516925152957144237)
              ·
                refine ⟨2521343068846932358929089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723581516925152957144237 2521343068846932358929089)
                ·
                  refine ⟨1891007301635199269196817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521343068846932358929089 1891007301635199269196817)
                  ·
                    refine ⟨1418255476226399451897613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1891007301635199269196817 1418255476226399451897613)
                    ·
                      refine ⟨531845803584899794461605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418255476226399451897613 531845803584899794461605)
                      ·
                        rfl

theorem cell23_1035766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1035766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035766 prefixEnd_1035766 := by exact prefixLift 1035766
  have htrace : WordTrace (prefixWord ++ tailWord_1035766) baseStart_1035766 baseEnd_1035766 := by
    simpa [prefixWord, tailWord_1035766, baseEnd_1035766] using wordTrace_append hprefix tailTrace_1035766
  have hstable : (prefixWord ++ tailWord_1035766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035766).length < 2 ^ (prefixWord ++ tailWord_1035766).sum := by decide
  have hdescent : baseEnd_1035766 < baseStart_1035766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035779 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 3]
def baseStart_1035779 : Nat := 118140960795 + 1035779 * 2 ^ 59
def prefixEnd_1035779 : Nat := 4983230072969 + 3 ^ 40 * 1035779 * 2
def baseEnd_1035779 : Nat := 531852478833408243599045

theorem tailTrace_1035779 : CollatzResearch.WordTrace tailWord_1035779 prefixEnd_1035779 531852478833408243599045 := by
  unfold tailWord_1035779
  simp only [CollatzResearch.WordTrace]
  refine ⟨37777963714557054814822391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25185309143038036543214927 37777963714557054814822391)
  ·
    refine ⟨56666945571835582222233587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37777963714557054814822391 56666945571835582222233587)
    ·
      refine ⟨85000418357753373333350381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56666945571835582222233587 85000418357753373333350381)
      ·
        refine ⟨31875156884157515000006393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85000418357753373333350381 31875156884157515000006393)
        ·
          refine ⟨23906367663118136250004795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31875156884157515000006393 23906367663118136250004795)
          ·
            refine ⟨35859551494677204375007193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906367663118136250004795 35859551494677204375007193)
            ·
              refine ⟨26894663621007903281255395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35859551494677204375007193 26894663621007903281255395)
              ·
                refine ⟨40341995431511854921883093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26894663621007903281255395 40341995431511854921883093)
                ·
                  refine ⟨945515517926059099731635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40341995431511854921883093 945515517926059099731635)
                  ·
                    refine ⟨1418273276889088649597453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945515517926059099731635 1418273276889088649597453)
                    ·
                      refine ⟨531852478833408243599045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418273276889088649597453 531852478833408243599045)
                      ·
                        rfl

theorem cell23_1035779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_1035779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035779 prefixEnd_1035779 := by exact prefixLift 1035779
  have htrace : WordTrace (prefixWord ++ tailWord_1035779) baseStart_1035779 baseEnd_1035779 := by
    simpa [prefixWord, tailWord_1035779, baseEnd_1035779] using wordTrace_append hprefix tailTrace_1035779
  have hstable : (prefixWord ++ tailWord_1035779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035779).length < 2 ^ (prefixWord ++ tailWord_1035779).sum := by decide
  have hdescent : baseEnd_1035779 < baseStart_1035779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035829 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1035829 : Nat := 118140960795 + 1035829 * 2 ^ 59
def prefixEnd_1035829 : Nat := 4983230072969 + 3 ^ 40 * 1035829 * 2
def baseEnd_1035829 : Nat := 177292717622044349324605

theorem tailTrace_1035829 : CollatzResearch.WordTrace tailWord_1035829 prefixEnd_1035829 177292717622044349324605 := by
  unfold tailWord_1035829
  simp only [CollatzResearch.WordTrace]
  refine ⟨37779787364375913354142541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25186524909583942236095027 37779787364375913354142541)
  ·
    refine ⟨14167420261640967507803453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37779787364375913354142541 14167420261640967507803453)
    ·
      refine ⟨5312782598115362815426295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14167420261640967507803453 5312782598115362815426295)
      ·
        refine ⟨7969173897173044223139443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312782598115362815426295 7969173897173044223139443)
        ·
          refine ⟨11953760845759566334709165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969173897173044223139443 11953760845759566334709165)
          ·
            refine ⟨4482660317159837375515937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11953760845759566334709165 4482660317159837375515937)
            ·
              refine ⟨3361995237869878031636953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482660317159837375515937 3361995237869878031636953)
              ·
                refine ⟨2521496428402408523727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361995237869878031636953 2521496428402408523727715)
                ·
                  refine ⟨3782244642603612785591573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521496428402408523727715 3782244642603612785591573)
                  ·
                    refine ⟨177292717622044349324605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3782244642603612785591573 177292717622044349324605)
                    ·
                      rfl

theorem cell23_1035829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1035829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035829 prefixEnd_1035829 := by exact prefixLift 1035829
  have htrace : WordTrace (prefixWord ++ tailWord_1035829) baseStart_1035829 baseEnd_1035829 := by
    simpa [prefixWord, tailWord_1035829, baseEnd_1035829] using wordTrace_append hprefix tailTrace_1035829
  have hstable : (prefixWord ++ tailWord_1035829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035829).length < 2 ^ (prefixWord ++ tailWord_1035829).sum := by decide
  have hdescent : baseEnd_1035829 < baseStart_1035829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035833 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_1035833 : Nat := 118140960795 + 1035833 * 2 ^ 59
def prefixEnd_1035833 : Nat := 4983230072969 + 3 ^ 40 * 1035833 * 2
def baseEnd_1035833 : Nat := 177293402262917010774599

theorem tailTrace_1035833 : CollatzResearch.WordTrace tailWord_1035833 prefixEnd_1035833 177293402262917010774599 := by
  unfold tailWord_1035833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37779933256361422037288153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25186622170907614691525435 37779933256361422037288153)
  ·
    refine ⟨28334949942271066527966115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37779933256361422037288153 28334949942271066527966115)
    ·
      refine ⟨42502424913406599791949173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28334949942271066527966115 42502424913406599791949173)
      ·
        refine ⟨3984602335631868730495235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42502424913406599791949173 3984602335631868730495235)
        ·
          refine ⟨5976903503447803095742853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984602335631868730495235 5976903503447803095742853)
          ·
            refine ⟨1120669406896463080451785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5976903503447803095742853 1120669406896463080451785)
            ·
              refine ⟨840502055172347310338839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120669406896463080451785 840502055172347310338839)
              ·
                refine ⟨1260753082758520965508259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840502055172347310338839 1260753082758520965508259)
                ·
                  refine ⟨1891129624137781448262389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260753082758520965508259 1891129624137781448262389)
                  ·
                    refine ⟨177293402262917010774599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891129624137781448262389 177293402262917010774599)
                    ·
                      rfl

theorem cell23_1035833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_1035833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035833 prefixEnd_1035833 := by exact prefixLift 1035833
  have htrace : WordTrace (prefixWord ++ tailWord_1035833) baseStart_1035833 baseEnd_1035833 := by
    simpa [prefixWord, tailWord_1035833, baseEnd_1035833] using wordTrace_append hprefix tailTrace_1035833
  have hstable : (prefixWord ++ tailWord_1035833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035833).length < 2 ^ (prefixWord ++ tailWord_1035833).sum := by decide
  have hdescent : baseEnd_1035833 < baseStart_1035833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035863 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 2, 4]
def baseStart_1035863 : Nat := 118140960795 + 1035863 * 2 ^ 59
def prefixEnd_1035863 : Nat := 4983230072969 + 3 ^ 40 * 1035863 * 2
def baseEnd_1035863 : Nat := 177298537069461971649553

theorem tailTrace_1035863 : CollatzResearch.WordTrace tailWord_1035863 prefixEnd_1035863 177298537069461971649553 := by
  unfold tailWord_1035863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781027446252737160880243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25187351630835158107253495 37781027446252737160880243)
  ·
    refine ⟨56671541169379105741320365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37781027446252737160880243 56671541169379105741320365)
    ·
      refine ⟨21251827938517164652995137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56671541169379105741320365 21251827938517164652995137)
      ·
        refine ⟨15938870953887873489746353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21251827938517164652995137 15938870953887873489746353)
        ·
          refine ⟨11954153215415905117309765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15938870953887873489746353 11954153215415905117309765)
          ·
            refine ⟨2241403727890482209495581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11954153215415905117309765 2241403727890482209495581)
            ·
              refine ⟨840526397958930828560843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2241403727890482209495581 840526397958930828560843)
              ·
                refine ⟨1260789596938396242841265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840526397958930828560843 1260789596938396242841265)
                ·
                  refine ⟨945592197703797182130949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260789596938396242841265 945592197703797182130949)
                  ·
                    refine ⟨177298537069461971649553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 945592197703797182130949 177298537069461971649553)
                    ·
                      rfl

theorem cell23_1035863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_1035863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035863 prefixEnd_1035863 := by exact prefixLift 1035863
  have htrace : WordTrace (prefixWord ++ tailWord_1035863) baseStart_1035863 baseEnd_1035863 := by
    simpa [prefixWord, tailWord_1035863, baseEnd_1035863] using wordTrace_append hprefix tailTrace_1035863
  have hstable : (prefixWord ++ tailWord_1035863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035863).length < 2 ^ (prefixWord ++ tailWord_1035863).sum := by decide
  have hdescent : baseEnd_1035863 < baseStart_1035863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035876 : List Nat := [2, 3, 1, 1, 2, 5, 2, 7]
def baseStart_1035876 : Nat := 118140960795 + 1035876 * 2 ^ 59
def prefixEnd_1035876 : Nat := 4983230072969 + 3 ^ 40 * 1035876 * 2
def baseEnd_1035876 : Nat := 19700084683588680151337

theorem tailTrace_1035876 : CollatzResearch.WordTrace tailWord_1035876 prefixEnd_1035876 19700084683588680151337 := by
  unfold tailWord_1035876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890750797602820190551741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25187667730137093587402321 18890750797602820190551741)
  ·
    refine ⟨7084031549101057571456903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18890750797602820190551741 7084031549101057571456903)
    ·
      refine ⟨10626047323651586357185355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7084031549101057571456903 10626047323651586357185355)
      ·
        refine ⟨15939070985477379535778033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626047323651586357185355 15939070985477379535778033)
        ·
          refine ⟨11954303239108034651833525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15939070985477379535778033 11954303239108034651833525)
          ·
            refine ⟨1120715928666378248609393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11954303239108034651833525 1120715928666378248609393)
            ·
              refine ⟨840536946499783686457045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120715928666378248609393 840536946499783686457045)
              ·
                refine ⟨19700084683588680151337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 840536946499783686457045 19700084683588680151337)
                ·
                  rfl

theorem cell23_1035876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 7].length) (baseStart_1035876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035876 prefixEnd_1035876 := by exact prefixLift 1035876
  have htrace : WordTrace (prefixWord ++ tailWord_1035876) baseStart_1035876 baseEnd_1035876 := by
    simpa [prefixWord, tailWord_1035876, baseEnd_1035876] using wordTrace_append hprefix tailTrace_1035876
  have hstable : (prefixWord ++ tailWord_1035876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035876).length < 2 ^ (prefixWord ++ tailWord_1035876).sum := by decide
  have hdescent : baseEnd_1035876 < baseStart_1035876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035909 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_1035909 : Nat := 118140960795 + 1035909 * 2 ^ 59
def prefixEnd_1035909 : Nat := 4983230072969 + 3 ^ 40 * 1035909 * 2
def baseEnd_1035909 : Nat := 531919231318492734973447

theorem tailTrace_1035909 : CollatzResearch.WordTrace tailWord_1035909 prefixEnd_1035909 531919231318492734973447 := by
  unfold tailWord_1035909
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782705204086087017054781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25188470136057391344703187 37782705204086087017054781)
  ·
    refine ⟨14168514451532282631395543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37782705204086087017054781 14168514451532282631395543)
    ·
      refine ⟨21252771677298423947093315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168514451532282631395543 21252771677298423947093315)
      ·
        refine ⟨31879157515947635920639973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21252771677298423947093315 31879157515947635920639973)
        ·
          refine ⟨5977342034240181735119995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31879157515947635920639973 5977342034240181735119995)
          ·
            refine ⟨8966013051360272602679993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977342034240181735119995 8966013051360272602679993)
            ·
              refine ⟨6724509788520204452009995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966013051360272602679993 6724509788520204452009995)
              ·
                refine ⟨10086764682780306678014993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724509788520204452009995 10086764682780306678014993)
                ·
                  refine ⟨7565073512085230008511245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10086764682780306678014993 7565073512085230008511245)
                  ·
                    refine ⟨2836902567031961253191717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7565073512085230008511245 2836902567031961253191717)
                    ·
                      refine ⟨531919231318492734973447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2836902567031961253191717 531919231318492734973447)
                      ·
                        rfl

theorem cell23_1035909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_1035909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035909 prefixEnd_1035909 := by exact prefixLift 1035909
  have htrace : WordTrace (prefixWord ++ tailWord_1035909) baseStart_1035909 baseEnd_1035909 := by
    simpa [prefixWord, tailWord_1035909, baseEnd_1035909] using wordTrace_append hprefix tailTrace_1035909
  have hstable : (prefixWord ++ tailWord_1035909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035909).length < 2 ^ (prefixWord ++ tailWord_1035909).sum := by decide
  have hdescent : baseEnd_1035909 < baseStart_1035909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035929 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_1035929 : Nat := 118140960795 + 1035929 * 2 ^ 59
def prefixEnd_1035929 : Nat := 4983230072969 + 3 ^ 40 * 1035929 * 2
def baseEnd_1035929 : Nat := 531929500931582656723355

theorem tailTrace_1035929 : CollatzResearch.WordTrace tailWord_1035929 prefixEnd_1035929 531929500931582656723355 := by
  unfold tailWord_1035929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37783434664013630432782841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25188956442675753621855227 37783434664013630432782841)
  ·
    refine ⟨28337575998010222824587131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37783434664013630432782841 28337575998010222824587131)
    ·
      refine ⟨42506363997015334236880697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28337575998010222824587131 42506363997015334236880697)
      ·
        refine ⟨31879772997761500677660523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42506363997015334236880697 31879772997761500677660523)
        ·
          refine ⟨47819659496642251016490785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31879772997761500677660523 47819659496642251016490785)
          ·
            refine ⟨35864744622481688262368089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47819659496642251016490785 35864744622481688262368089)
            ·
              refine ⟨26898558466861266196776067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35864744622481688262368089 26898558466861266196776067)
              ·
                refine ⟨40347837700291899295164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26898558466861266196776067 40347837700291899295164101)
                ·
                  refine ⟨7565219568804731117843269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40347837700291899295164101 7565219568804731117843269)
                  ·
                    refine ⟨1418478669150887084595613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565219568804731117843269 1418478669150887084595613)
                    ·
                      refine ⟨531929500931582656723355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418478669150887084595613 531929500931582656723355)
                      ·
                        rfl

theorem cell23_1035929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_1035929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035929 prefixEnd_1035929 := by exact prefixLift 1035929
  have htrace : WordTrace (prefixWord ++ tailWord_1035929) baseStart_1035929 baseEnd_1035929 := by
    simpa [prefixWord, tailWord_1035929, baseEnd_1035929] using wordTrace_append hprefix tailTrace_1035929
  have hstable : (prefixWord ++ tailWord_1035929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035929).length < 2 ^ (prefixWord ++ tailWord_1035929).sum := by decide
  have hdescent : baseEnd_1035929 < baseStart_1035929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035976 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1035976 : Nat := 118140960795 + 1035976 * 2 ^ 59
def prefixEnd_1035976 : Nat := 4983230072969 + 3 ^ 40 * 1035976 * 2
def baseEnd_1035976 : Nat := 531953634522343972835639

theorem tailTrace_1035976 : CollatzResearch.WordTrace tailWord_1035976 prefixEnd_1035976 531953634522343972835639 := by
  unfold tailWord_1035976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892574447421678729871891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25190099263228904973162521 18892574447421678729871891)
  ·
    refine ⟨28338861671132518094807837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18892574447421678729871891 28338861671132518094807837)
    ·
      refine ⟨10627073126674694285552939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28338861671132518094807837 10627073126674694285552939)
      ·
        refine ⟨15940609690012041428329409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627073126674694285552939 15940609690012041428329409)
        ·
          refine ⟨11955457267509031071247057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15940609690012041428329409 11955457267509031071247057)
          ·
            refine ⟨8966592950631773303435293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955457267509031071247057 8966592950631773303435293)
            ·
              refine ⟨3362472356486914988788235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966592950631773303435293 3362472356486914988788235)
              ·
                refine ⟨5043708534730372483182353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362472356486914988788235 5043708534730372483182353)
                ·
                  refine ⟨3782781401047779362386765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043708534730372483182353 3782781401047779362386765)
                  ·
                    refine ⟨1418543025392917260895037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782781401047779362386765 1418543025392917260895037)
                    ·
                      refine ⟨531953634522343972835639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418543025392917260895037 531953634522343972835639)
                      ·
                        rfl

theorem cell23_1035976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1035976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035976 prefixEnd_1035976 := by exact prefixLift 1035976
  have htrace : WordTrace (prefixWord ++ tailWord_1035976) baseStart_1035976 baseEnd_1035976 := by
    simpa [prefixWord, tailWord_1035976, baseEnd_1035976] using wordTrace_append hprefix tailTrace_1035976
  have hstable : (prefixWord ++ tailWord_1035976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035976).length < 2 ^ (prefixWord ++ tailWord_1035976).sum := by decide
  have hdescent : baseEnd_1035976 < baseStart_1035976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035979 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 4, 5]
def baseStart_1035979 : Nat := 118140960795 + 1035979 * 2 ^ 59
def prefixEnd_1035979 : Nat := 4983230072969 + 3 ^ 40 * 1035979 * 2
def baseEnd_1035979 : Nat := 177318391654769153699375

theorem tailTrace_1035979 : CollatzResearch.WordTrace tailWord_1035979 prefixEnd_1035979 177318391654769153699375 := by
  unfold tailWord_1035979
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785258313832488972102991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25190172209221659314735327 37785258313832488972102991)
  ·
    refine ⟨56677887470748733458154487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37785258313832488972102991 56677887470748733458154487)
    ·
      refine ⟨85016831206123100187231731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56677887470748733458154487 85016831206123100187231731)
      ·
        refine ⟨127525246809184650280847597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85016831206123100187231731 127525246809184650280847597)
        ·
          refine ⟨47821967553444243855317849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127525246809184650280847597 47821967553444243855317849)
          ·
            refine ⟨35866475665083182891488387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47821967553444243855317849 35866475665083182891488387)
            ·
              refine ⟨53799713497624774337232581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35866475665083182891488387 53799713497624774337232581)
              ·
                refine ⟨10087446280804645188231109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53799713497624774337232581 10087446280804645188231109)
                ·
                  refine ⟨1891396177650870972793333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10087446280804645188231109 1891396177650870972793333)
                  ·
                    refine ⟨177318391654769153699375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891396177650870972793333 177318391654769153699375)
                    ·
                      rfl

theorem cell23_1035979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].length) (baseStart_1035979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1035979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1035979 prefixEnd_1035979 := by exact prefixLift 1035979
  have htrace : WordTrace (prefixWord ++ tailWord_1035979) baseStart_1035979 baseEnd_1035979 := by
    simpa [prefixWord, tailWord_1035979, baseEnd_1035979] using wordTrace_append hprefix tailTrace_1035979
  have hstable : (prefixWord ++ tailWord_1035979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035979).length < 2 ^ (prefixWord ++ tailWord_1035979).sum := by decide
  have hdescent : baseEnd_1035979 < baseStart_1035979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036019 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1036019 : Nat := 118140960795 + 1036019 * 2 ^ 59
def prefixEnd_1036019 : Nat := 4983230072969 + 3 ^ 40 * 1036019 * 2
def baseEnd_1036019 : Nat := 531975714190487304597941

theorem tailTrace_1036019 : CollatzResearch.WordTrace tailWord_1036019 prefixEnd_1036019 531975714190487304597941 := by
  unfold tailWord_1036019
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786717233687575803559111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25191144822458383869039407 37786717233687575803559111)
  ·
    refine ⟨56680075850531363705338667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37786717233687575803559111 56680075850531363705338667)
    ·
      refine ⟨85020113775797045558008001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56680075850531363705338667 85020113775797045558008001)
      ·
        refine ⟨63765085331847784168506001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85020113775797045558008001 63765085331847784168506001)
        ·
          refine ⟨47823813998885838126379501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63765085331847784168506001 47823813998885838126379501)
          ·
            refine ⟨17933930249582189297392313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47823813998885838126379501 17933930249582189297392313)
            ·
              refine ⟨13450447687186641973044235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17933930249582189297392313 13450447687186641973044235)
              ·
                refine ⟨20175671530779962959566353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450447687186641973044235 20175671530779962959566353)
                ·
                  refine ⟨15131753648084972219674765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20175671530779962959566353 15131753648084972219674765)
                  ·
                    refine ⟨5674407618031864582378037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15131753648084972219674765 5674407618031864582378037)
                    ·
                      refine ⟨531975714190487304597941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5674407618031864582378037 531975714190487304597941)
                      ·
                        rfl

theorem cell23_1036019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1036019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036019 prefixEnd_1036019 := by exact prefixLift 1036019
  have htrace : WordTrace (prefixWord ++ tailWord_1036019) baseStart_1036019 baseEnd_1036019 := by
    simpa [prefixWord, tailWord_1036019, baseEnd_1036019] using wordTrace_append hprefix tailTrace_1036019
  have hstable : (prefixWord ++ tailWord_1036019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036019).length < 2 ^ (prefixWord ++ tailWord_1036019).sum := by decide
  have hdescent : baseEnd_1036019 < baseStart_1036019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036033 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_1036033 : Nat := 118140960795 + 1036033 * 2 ^ 59
def prefixEnd_1036033 : Nat := 4983230072969 + 3 ^ 40 * 1036033 * 2
def baseEnd_1036033 : Nat := 531982902919650249822877

theorem tailTrace_1036033 : CollatzResearch.WordTrace tailWord_1036033 prefixEnd_1036033 531982902919650249822877 := by
  unfold tailWord_1036033
  simp only [CollatzResearch.WordTrace]
  refine ⟨37787227855636856194568753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25191485237091237463045835 37787227855636856194568753)
  ·
    refine ⟨28340420891727642145926565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37787227855636856194568753 28340420891727642145926565)
    ·
      refine ⟨5313828917198932902361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28340420891727642145926565 5313828917198932902361231)
      ·
        refine ⟨7970743375798399353541847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313828917198932902361231 7970743375798399353541847)
        ·
          refine ⟨11956115063697599030312771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970743375798399353541847 11956115063697599030312771)
          ·
            refine ⟨17934172595546398545469157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956115063697599030312771 17934172595546398545469157)
            ·
              refine ⟨3362657361664949727275467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17934172595546398545469157 3362657361664949727275467)
              ·
                refine ⟨5043986042497424590913201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362657361664949727275467 5043986042497424590913201)
                ·
                  refine ⟨3782989531873068443184901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043986042497424590913201 3782989531873068443184901)
                  ·
                    refine ⟨709310537226200333097169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782989531873068443184901 709310537226200333097169)
                    ·
                      refine ⟨531982902919650249822877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709310537226200333097169 531982902919650249822877)
                      ·
                        rfl

theorem cell23_1036033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_1036033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036033 prefixEnd_1036033 := by exact prefixLift 1036033
  have htrace : WordTrace (prefixWord ++ tailWord_1036033) baseStart_1036033 baseEnd_1036033 := by
    simpa [prefixWord, tailWord_1036033, baseEnd_1036033] using wordTrace_append hprefix tailTrace_1036033
  have hstable : (prefixWord ++ tailWord_1036033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036033).length < 2 ^ (prefixWord ++ tailWord_1036033).sum := by decide
  have hdescent : baseEnd_1036033 < baseStart_1036033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
