import V185TrunkScan20Chunk088

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_542285 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 2]
def baseStart_542285 : Nat := 118140960795 + 542285 * 2 ^ 59
def prefixEnd_542285 : Nat := 4983230072969 + 3 ^ 40 * 542285 * 2
def baseEnd_542285 : Nat := 247513650420903147683185

theorem tailTrace_542285 : CollatzResearch.WordTrace tailWord_542285 prefixEnd_542285 247513650420903147683185 := by
  unfold tailWord_542285
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778758840401534749660309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13185839226934356499773539 19778758840401534749660309)
  ·
    refine ⟨927129320643821941390327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19778758840401534749660309 927129320643821941390327)
    ·
      refine ⟨1390693980965732912085491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927129320643821941390327 1390693980965732912085491)
      ·
        refine ⟨2086040971448599368128237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390693980965732912085491 2086040971448599368128237)
        ·
          refine ⟨782265364293224763048089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086040971448599368128237 782265364293224763048089)
          ·
            refine ⟨586699023219918572286067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782265364293224763048089 586699023219918572286067)
            ·
              refine ⟨880048534829877858429101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586699023219918572286067 880048534829877858429101)
              ·
                refine ⟨330018200561204196910913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880048534829877858429101 330018200561204196910913)
                ·
                  refine ⟨247513650420903147683185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330018200561204196910913 247513650420903147683185)
                  ·
                    rfl

theorem cell20_542285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_542285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542285 prefixEnd_542285 := by exact prefixLift 542285
  have htrace : WordTrace (prefixWord ++ tailWord_542285) baseStart_542285 baseEnd_542285 := by
    simpa [prefixWord, tailWord_542285, baseEnd_542285] using wordTrace_append hprefix tailTrace_542285
  have hstable : (prefixWord ++ tailWord_542285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542285).length < 2 ^ (prefixWord ++ tailWord_542285).sum := by decide
  have hdescent : baseEnd_542285 < baseStart_542285 := by decide
  rcases family_descends (prefixWord ++ tailWord_542285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542320 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_542320 : Nat := 118140960795 + 542320 * 2 ^ 59
def prefixEnd_542320 : Nat := 4983230072969 + 3 ^ 40 * 542320 * 2
def baseEnd_542320 : Nat := 247529625374598581516375

theorem tailTrace_542320 : CollatzResearch.WordTrace tailWord_542320 prefixEnd_542320 247529625374598581516375 := by
  unfold tailWord_542320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890017697637367863592207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13186690263516490484789609 9890017697637367863592207)
  ·
    refine ⟨14835026546456051795388311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890017697637367863592207 14835026546456051795388311)
    ·
      refine ⟨22252539819684077693082467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835026546456051795388311 22252539819684077693082467)
      ·
        refine ⟨33378809729526116539623701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22252539819684077693082467 33378809729526116539623701)
        ·
          refine ⟨1564631706071536712794861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33378809729526116539623701 1564631706071536712794861)
          ·
            refine ⟨586736889776826267298073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564631706071536712794861 586736889776826267298073)
            ·
              refine ⟨440052667332619700473555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586736889776826267298073 440052667332619700473555)
              ·
                refine ⟨660079000998929550710333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440052667332619700473555 660079000998929550710333)
                ·
                  refine ⟨247529625374598581516375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660079000998929550710333 247529625374598581516375)
                  ·
                    rfl

theorem cell20_542320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_542320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542320 prefixEnd_542320 := by exact prefixLift 542320
  have htrace : WordTrace (prefixWord ++ tailWord_542320) baseStart_542320 baseEnd_542320 := by
    simpa [prefixWord, tailWord_542320, baseEnd_542320] using wordTrace_append hprefix tailTrace_542320
  have hstable : (prefixWord ++ tailWord_542320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542320).length < 2 ^ (prefixWord ++ tailWord_542320).sum := by decide
  have hdescent : baseEnd_542320 < baseStart_542320 := by decide
  rcases family_descends (prefixWord ++ tailWord_542320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542345 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_542345 : Nat := 118140960795 + 542345 * 2 ^ 59
def prefixEnd_542345 : Nat := 4983230072969 + 3 ^ 40 * 542345 * 2
def baseEnd_542345 : Nat := 247541036055809605682939

theorem tailTrace_542345 : CollatzResearch.WordTrace tailWord_542345 prefixEnd_542345 247541036055809605682939 := by
  unfold tailWord_542345
  simp only [CollatzResearch.WordTrace]
  refine ⟨19780947220184164996844489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13187298146789443331229659 19780947220184164996844489)
  ·
    refine ⟨14835710415138123747633367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19780947220184164996844489 14835710415138123747633367)
    ·
      refine ⟨22253565622707185621450051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835710415138123747633367 22253565622707185621450051)
      ·
        refine ⟨33380348434060778432175077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22253565622707185621450051 33380348434060778432175077)
        ·
          refine ⟨6258815331386395956032827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33380348434060778432175077 6258815331386395956032827)
          ·
            refine ⟨9388222997079593934049241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6258815331386395956032827 9388222997079593934049241)
            ·
              refine ⟨7041167247809695450536931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9388222997079593934049241 7041167247809695450536931)
              ·
                refine ⟨10561750871714543175805397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7041167247809695450536931 10561750871714543175805397)
                ·
                  refine ⟨247541036055809605682939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10561750871714543175805397 247541036055809605682939)
                  ·
                    rfl

theorem cell20_542345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_542345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542345 prefixEnd_542345 := by exact prefixLift 542345
  have htrace : WordTrace (prefixWord ++ tailWord_542345) baseStart_542345 baseEnd_542345 := by
    simpa [prefixWord, tailWord_542345, baseEnd_542345] using wordTrace_append hprefix tailTrace_542345
  have hstable : (prefixWord ++ tailWord_542345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542345).length < 2 ^ (prefixWord ++ tailWord_542345).sum := by decide
  have hdescent : baseEnd_542345 < baseStart_542345 := by decide
  rcases family_descends (prefixWord ++ tailWord_542345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542348 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_542348 : Nat := 118140960795 + 542348 * 2 ^ 59
def prefixEnd_542348 : Nat := 4983230072969 + 3 ^ 40 * 542348 * 2
def baseEnd_542348 : Nat := 247542405337554928582927

theorem tailTrace_542348 : CollatzResearch.WordTrace tailWord_542348 prefixEnd_542348 247542405337554928582927 := by
  unfold tailWord_542348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890528319586648254601849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13187371092782197672802465 9890528319586648254601849)
  ·
    refine ⟨7417896239689986190951387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9890528319586648254601849 7417896239689986190951387)
    ·
      refine ⟨11126844359534979286427081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7417896239689986190951387 11126844359534979286427081)
      ·
        refine ⟨8345133269651234464820311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11126844359534979286427081 8345133269651234464820311)
        ·
          refine ⟨12517699904476851697230467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345133269651234464820311 12517699904476851697230467)
          ·
            refine ⟨18776549856715277545845701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12517699904476851697230467 18776549856715277545845701)
            ·
              refine ⟨3520603098134114539846069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18776549856715277545845701 3520603098134114539846069)
              ·
                refine ⟨330056540450073238110569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3520603098134114539846069 330056540450073238110569)
                ·
                  refine ⟨247542405337554928582927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330056540450073238110569 247542405337554928582927)
                  ·
                    rfl

theorem cell20_542348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_542348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542348 prefixEnd_542348 := by exact prefixLift 542348
  have htrace : WordTrace (prefixWord ++ tailWord_542348) baseStart_542348 baseEnd_542348 := by
    simpa [prefixWord, tailWord_542348, baseEnd_542348] using wordTrace_append hprefix tailTrace_542348
  have hstable : (prefixWord ++ tailWord_542348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542348).length < 2 ^ (prefixWord ++ tailWord_542348).sum := by decide
  have hdescent : baseEnd_542348 < baseStart_542348 := by decide
  rcases family_descends (prefixWord ++ tailWord_542348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542413 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_542413 : Nat := 118140960795 + 542413 * 2 ^ 59
def prefixEnd_542413 : Nat := 4983230072969 + 3 ^ 40 * 542413 * 2
def baseEnd_542413 : Nat := 247572073108703591415995

theorem tailTrace_542413 : CollatzResearch.WordTrace tailWord_542413 prefixEnd_542413 247572073108703591415995 := by
  unfold tailWord_542413
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783427383937812610319893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13188951589291875073546595 19783427383937812610319893)
  ·
    refine ⟨927348158622084966108745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19783427383937812610319893 927348158622084966108745)
    ·
      refine ⟨695511118966563724581559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927348158622084966108745 695511118966563724581559)
      ·
        refine ⟨1043266678449845586872339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695511118966563724581559 1043266678449845586872339)
        ·
          refine ⟨1564900017674768380308509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043266678449845586872339 1564900017674768380308509)
          ·
            refine ⟨586837506628038142615691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564900017674768380308509 586837506628038142615691)
            ·
              refine ⟨880256259942057213923537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586837506628038142615691 880256259942057213923537)
              ·
                refine ⟨660192194956542910442653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880256259942057213923537 660192194956542910442653)
                ·
                  refine ⟨247572073108703591415995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660192194956542910442653 247572073108703591415995)
                  ·
                    rfl

theorem cell20_542413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_542413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542413 prefixEnd_542413 := by exact prefixLift 542413
  have htrace : WordTrace (prefixWord ++ tailWord_542413) baseStart_542413 baseEnd_542413 := by
    simpa [prefixWord, tailWord_542413, baseEnd_542413] using wordTrace_append hprefix tailTrace_542413
  have hstable : (prefixWord ++ tailWord_542413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542413).length < 2 ^ (prefixWord ++ tailWord_542413).sum := by decide
  have hdescent : baseEnd_542413 < baseStart_542413 := by decide
  rcases family_descends (prefixWord ++ tailWord_542413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542414 : List Nat := [4, 1, 1, 1, 3, 1, 9]
def baseStart_542414 : Nat := 118140960795 + 542414 * 2 ^ 59
def prefixEnd_542414 : Nat := 4983230072969 + 3 ^ 40 * 542414 * 2
def baseEnd_542414 : Nat := 27508058837328003598073

theorem tailTrace_542414 : CollatzResearch.WordTrace tailWord_542414 prefixEnd_542414 27508058837328003598073 := by
  unfold tailWord_542414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472932982116773722638287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13188975904622793187404197 2472932982116773722638287)
  ·
    refine ⟨3709399473175160583957431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472932982116773722638287 3709399473175160583957431)
    ·
      refine ⟨5564099209762740875936147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709399473175160583957431 5564099209762740875936147)
      ·
        refine ⟨8346148814644111313904221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564099209762740875936147 8346148814644111313904221)
        ·
          refine ⟨3129805805491541742714083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8346148814644111313904221 3129805805491541742714083)
          ·
            refine ⟨4694708708237312614071125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129805805491541742714083 4694708708237312614071125)
            ·
              refine ⟨27508058837328003598073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4694708708237312614071125 27508058837328003598073)
              ·
                rfl

theorem cell20_542414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_542414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542414 prefixEnd_542414 := by exact prefixLift 542414
  have htrace : WordTrace (prefixWord ++ tailWord_542414) baseStart_542414 baseEnd_542414 := by
    simpa [prefixWord, tailWord_542414, baseEnd_542414] using wordTrace_append hprefix tailTrace_542414
  have hstable : (prefixWord ++ tailWord_542414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542414).length < 2 ^ (prefixWord ++ tailWord_542414).sum := by decide
  have hdescent : baseEnd_542414 < baseStart_542414 := by decide
  rcases family_descends (prefixWord ++ tailWord_542414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542417 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_542417 : Nat := 118140960795 + 542417 * 2 ^ 59
def prefixEnd_542417 : Nat := 4983230072969 + 3 ^ 40 * 542417 * 2
def baseEnd_542417 : Nat := 247573898817697355282645

theorem tailTrace_542417 : CollatzResearch.WordTrace tailWord_542417 prefixEnd_542417 247573898817697355282645 := by
  unfold tailWord_542417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783573275923321293465505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13189048850615547528977003 19783573275923321293465505)
  ·
    refine ⟨14837679956942490970099129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783573275923321293465505 14837679956942490970099129)
    ·
      refine ⟨11128259967706868227574347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14837679956942490970099129 11128259967706868227574347)
      ·
        refine ⟨16692389951560302341361521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128259967706868227574347 16692389951560302341361521)
        ·
          refine ⟨12519292463670226756021141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16692389951560302341361521 12519292463670226756021141)
          ·
            refine ⟨586841834234541879188491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12519292463670226756021141 586841834234541879188491)
            ·
              refine ⟨880262751351812818782737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586841834234541879188491 880262751351812818782737)
              ·
                refine ⟨660197063513859614087053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880262751351812818782737 660197063513859614087053)
                ·
                  refine ⟨247573898817697355282645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660197063513859614087053 247573898817697355282645)
                  ·
                    rfl

theorem cell20_542417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_542417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542417 prefixEnd_542417 := by exact prefixLift 542417
  have htrace : WordTrace (prefixWord ++ tailWord_542417) baseStart_542417 baseEnd_542417 := by
    simpa [prefixWord, tailWord_542417, baseEnd_542417] using wordTrace_append hprefix tailTrace_542417
  have hstable : (prefixWord ++ tailWord_542417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542417).length < 2 ^ (prefixWord ++ tailWord_542417).sum := by decide
  have hdescent : baseEnd_542417 < baseStart_542417 := by decide
  rcases family_descends (prefixWord ++ tailWord_542417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542424 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_542424 : Nat := 118140960795 + 542424 * 2 ^ 59
def prefixEnd_542424 : Nat := 4983230072969 + 3 ^ 40 * 542424 * 2
def baseEnd_542424 : Nat := 247577093808436442049283

theorem tailTrace_542424 : CollatzResearch.WordTrace tailWord_542424 prefixEnd_542424 247577093808436442049283 := by
  unfold tailWord_542424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891914293448980744485163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13189219057931974325980217 9891914293448980744485163)
  ·
    refine ⟨14837871440173471116727745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9891914293448980744485163 14837871440173471116727745)
    ·
      refine ⟨11128403580130103337545809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14837871440173471116727745 11128403580130103337545809)
      ·
        refine ⟨8346302685097577503159357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11128403580130103337545809 8346302685097577503159357)
        ·
          refine ⟨3129863506911591563684759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8346302685097577503159357 3129863506911591563684759)
          ·
            refine ⟨4694795260367387345527139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129863506911591563684759 4694795260367387345527139)
            ·
              refine ⟨7042192890551081018290709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694795260367387345527139 7042192890551081018290709)
              ·
                refine ⟨330102791744581922732377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7042192890551081018290709 330102791744581922732377)
                ·
                  refine ⟨247577093808436442049283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330102791744581922732377 247577093808436442049283)
                  ·
                    rfl

theorem cell20_542424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_542424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542424 prefixEnd_542424 := by exact prefixLift 542424
  have htrace : WordTrace (prefixWord ++ tailWord_542424) baseStart_542424 baseEnd_542424 := by
    simpa [prefixWord, tailWord_542424, baseEnd_542424] using wordTrace_append hprefix tailTrace_542424
  have hstable : (prefixWord ++ tailWord_542424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542424).length < 2 ^ (prefixWord ++ tailWord_542424).sum := by decide
  have hdescent : baseEnd_542424 < baseStart_542424 := by decide
  rcases family_descends (prefixWord ++ tailWord_542424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542490 : List Nat := [3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_542490 : Nat := 118140960795 + 542490 * 2 ^ 59
def prefixEnd_542490 : Nat := 4983230072969 + 3 ^ 40 * 542490 * 2
def baseEnd_542490 : Nat := 82535739335611181949671

theorem tailTrace_542490 : CollatzResearch.WordTrace tailWord_542490 prefixEnd_542490 82535739335611181949671 := by
  unfold tailWord_542490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946558951164713690218231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13190823869772569840581949 4946558951164713690218231)
  ·
    refine ⟨7419838426747070535327347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946558951164713690218231 7419838426747070535327347)
    ·
      refine ⟨11129757640120605802991021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419838426747070535327347 11129757640120605802991021)
      ·
        refine ⟨4173659115045227176121633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11129757640120605802991021 4173659115045227176121633)
        ·
          refine ⟨3130244336283920382091225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4173659115045227176121633 3130244336283920382091225)
          ·
            refine ⟨2347683252212940286568419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3130244336283920382091225 2347683252212940286568419)
            ·
              refine ⟨3521524878319410429852629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347683252212940286568419 3521524878319410429852629)
              ·
                refine ⟨82535739335611181949671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3521524878319410429852629 82535739335611181949671)
                ·
                  rfl

theorem cell20_542490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_542490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542490 prefixEnd_542490 := by exact prefixLift 542490
  have htrace : WordTrace (prefixWord ++ tailWord_542490) baseStart_542490 baseEnd_542490 := by
    simpa [prefixWord, tailWord_542490, baseEnd_542490] using wordTrace_append hprefix tailTrace_542490
  have hstable : (prefixWord ++ tailWord_542490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542490).length < 2 ^ (prefixWord ++ tailWord_542490).sum := by decide
  have hdescent : baseEnd_542490 < baseStart_542490 := by decide
  rcases family_descends (prefixWord ++ tailWord_542490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542535 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_542535 : Nat := 118140960795 + 542535 * 2 ^ 59
def prefixEnd_542535 : Nat := 4983230072969 + 3 ^ 40 * 542535 * 2
def baseEnd_542535 : Nat := 247627757233013389348829

theorem tailTrace_542535 : CollatzResearch.WordTrace tailWord_542535 prefixEnd_542535 247627757233013389348829 := by
  unfold tailWord_542535
  simp only [CollatzResearch.WordTrace]
  refine ⟨19787877089495827446261059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13191918059663884964174039 19787877089495827446261059)
  ·
    refine ⟨29681815634243741169391589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19787877089495827446261059 29681815634243741169391589)
    ·
      refine ⟨5565340431420701469260923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29681815634243741169391589 5565340431420701469260923)
      ·
        refine ⟨8348010647131052203891385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565340431420701469260923 8348010647131052203891385)
        ·
          refine ⟨6261007985348289152918539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8348010647131052203891385 6261007985348289152918539)
          ·
            refine ⟨9391511978022433729377809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6261007985348289152918539 9391511978022433729377809)
            ·
              refine ⟨7043633983516825297033357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9391511978022433729377809 7043633983516825297033357)
              ·
                refine ⟨2641362743818809486387509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7043633983516825297033357 2641362743818809486387509)
                ·
                  refine ⟨247627757233013389348829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641362743818809486387509 247627757233013389348829)
                  ·
                    rfl

theorem cell20_542535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_542535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542535 prefixEnd_542535 := by exact prefixLift 542535
  have htrace : WordTrace (prefixWord ++ tailWord_542535) baseStart_542535 baseEnd_542535 := by
    simpa [prefixWord, tailWord_542535, baseEnd_542535] using wordTrace_append hprefix tailTrace_542535
  have hstable : (prefixWord ++ tailWord_542535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542535).length < 2 ^ (prefixWord ++ tailWord_542535).sum := by decide
  have hdescent : baseEnd_542535 < baseStart_542535 := by decide
  rcases family_descends (prefixWord ++ tailWord_542535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542538 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_542538 : Nat := 118140960795 + 542538 * 2 ^ 59
def prefixEnd_542538 : Nat := 4983230072969 + 3 ^ 40 * 542538 * 2
def baseEnd_542538 : Nat := 247629126514758712248817

theorem tailTrace_542538 : CollatzResearch.WordTrace tailWord_542538 prefixEnd_542538 247629126514758712248817 := by
  unfold tailWord_542538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946996627121239739655067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13191991005656639305746845 4946996627121239739655067)
  ·
    refine ⟨7420494940681859609482601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946996627121239739655067 7420494940681859609482601)
    ·
      refine ⟨5565371205511394707111951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7420494940681859609482601 5565371205511394707111951)
      ·
        refine ⟨8348056808267092060667927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565371205511394707111951 8348056808267092060667927)
        ·
          refine ⟨12522085212400638091001891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8348056808267092060667927 12522085212400638091001891)
          ·
            refine ⟨18783127818600957136502837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12522085212400638091001891 18783127818600957136502837)
            ·
              refine ⟨1760918232993839731547141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18783127818600957136502837 1760918232993839731547141)
              ·
                refine ⟨330172168686344949665089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1760918232993839731547141 330172168686344949665089)
                ·
                  refine ⟨247629126514758712248817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330172168686344949665089 247629126514758712248817)
                  ·
                    rfl

theorem cell20_542538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_542538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542538 prefixEnd_542538 := by exact prefixLift 542538
  have htrace : WordTrace (prefixWord ++ tailWord_542538) baseStart_542538 baseEnd_542538 := by
    simpa [prefixWord, tailWord_542538, baseEnd_542538] using wordTrace_append hprefix tailTrace_542538
  have hstable : (prefixWord ++ tailWord_542538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542538).length < 2 ^ (prefixWord ++ tailWord_542538).sum := by decide
  have hdescent : baseEnd_542538 < baseStart_542538 := by decide
  rcases family_descends (prefixWord ++ tailWord_542538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542545 : List Nat := [1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_542545 : Nat := 118140960795 + 542545 * 2 ^ 59
def prefixEnd_542545 : Nat := 4983230072969 + 3 ^ 40 * 542545 * 2
def baseEnd_542545 : Nat := 82544107168499266338485

theorem tailTrace_542545 : CollatzResearch.WordTrace tailWord_542545 prefixEnd_542545 82544107168499266338485 := by
  unfold tailWord_542545
  simp only [CollatzResearch.WordTrace]
  refine ⟨19788241819459599154125089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13192161212973066102750059 19788241819459599154125089)
  ·
    refine ⟨14841181364594699365593817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19788241819459599154125089 14841181364594699365593817)
    ·
      refine ⟨11130886023446024524195363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14841181364594699365593817 11130886023446024524195363)
      ·
        refine ⟨16696329035169036786293045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11130886023446024524195363 16696329035169036786293045)
        ·
          refine ⟨1565280847047097198714973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16696329035169036786293045 1565280847047097198714973)
          ·
            refine ⟨586980317642661449518115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1565280847047097198714973 586980317642661449518115)
            ·
              refine ⟨880470476463992174277173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586980317642661449518115 880470476463992174277173)
              ·
                refine ⟨82544107168499266338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 880470476463992174277173 82544107168499266338485)
                ·
                  rfl

theorem cell20_542545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_542545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542545 prefixEnd_542545 := by exact prefixLift 542545
  have htrace : WordTrace (prefixWord ++ tailWord_542545) baseStart_542545 baseEnd_542545 := by
    simpa [prefixWord, tailWord_542545, baseEnd_542545] using wordTrace_append hprefix tailTrace_542545
  have hstable : (prefixWord ++ tailWord_542545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542545).length < 2 ^ (prefixWord ++ tailWord_542545).sum := by decide
  have hdescent : baseEnd_542545 < baseStart_542545 := by decide
  rcases family_descends (prefixWord ++ tailWord_542545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542559 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_542559 : Nat := 118140960795 + 542559 * 2 ^ 59
def prefixEnd_542559 : Nat := 4983230072969 + 3 ^ 40 * 542559 * 2
def baseEnd_542559 : Nat := 247638711486975972548731

theorem tailTrace_542559 : CollatzResearch.WordTrace tailWord_542559 prefixEnd_542559 247638711486975972548731 := by
  unfold tailWord_542559
  simp only [CollatzResearch.WordTrace]
  refine ⟨19788752441408879545134731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13192501627605919696756487 19788752441408879545134731)
  ·
    refine ⟨29683128662113319317702097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19788752441408879545134731 29683128662113319317702097)
    ·
      refine ⟨22262346496584989488276573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29683128662113319317702097 22262346496584989488276573)
      ·
        refine ⟨8348379936219371058103715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22262346496584989488276573 8348379936219371058103715)
        ·
          refine ⟨12522569904329056587155573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8348379936219371058103715 12522569904329056587155573)
          ·
            refine ⟨1173990928530849055045835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12522569904329056587155573 1173990928530849055045835)
            ·
              refine ⟨1760986392796273582568753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173990928530849055045835 1760986392796273582568753)
              ·
                refine ⟨1320739794597205186926565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760986392796273582568753 1320739794597205186926565)
                ·
                  refine ⟨247638711486975972548731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320739794597205186926565 247638711486975972548731)
                  ·
                    rfl

theorem cell20_542559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_542559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542559 prefixEnd_542559 := by exact prefixLift 542559
  have htrace : WordTrace (prefixWord ++ tailWord_542559) baseStart_542559 baseEnd_542559 := by
    simpa [prefixWord, tailWord_542559, baseEnd_542559] using wordTrace_append hprefix tailTrace_542559
  have hstable : (prefixWord ++ tailWord_542559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542559).length < 2 ^ (prefixWord ++ tailWord_542559).sum := by decide
  have hdescent : baseEnd_542559 < baseStart_542559 := by decide
  rcases family_descends (prefixWord ++ tailWord_542559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542562 : List Nat := [3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_542562 : Nat := 118140960795 + 542562 * 2 ^ 59
def prefixEnd_542562 : Nat := 4983230072969 + 3 ^ 40 * 542562 * 2
def baseEnd_542562 : Nat := 82546693589573765149573

theorem tailTrace_542562 : CollatzResearch.WordTrace tailWord_542562 prefixEnd_542562 82546693589573765149573 := by
  unfold tailWord_542562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947215465099502764373485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13192574573598674038329293 4947215465099502764373485)
  ·
    refine ⟨1855205799412313536640057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4947215465099502764373485 1855205799412313536640057)
    ·
      refine ⟨1391404349559235152480043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855205799412313536640057 1391404349559235152480043)
      ·
        refine ⟨2087106524338852728720065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391404349559235152480043 2087106524338852728720065)
        ·
          refine ⟨1565329893254139546540049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087106524338852728720065 1565329893254139546540049)
          ·
            refine ⟨1173997419940604659905037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1565329893254139546540049 1173997419940604659905037)
            ·
              refine ⟨440249032477726747464389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1173997419940604659905037 440249032477726747464389)
              ·
                refine ⟨82546693589573765149573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440249032477726747464389 82546693589573765149573)
                ·
                  rfl

theorem cell20_542562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_542562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542562 prefixEnd_542562 := by exact prefixLift 542562
  have htrace : WordTrace (prefixWord ++ tailWord_542562) baseStart_542562 baseEnd_542562 := by
    simpa [prefixWord, tailWord_542562, baseEnd_542562] using wordTrace_append hprefix tailTrace_542562
  have hstable : (prefixWord ++ tailWord_542562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542562).length < 2 ^ (prefixWord ++ tailWord_542562).sum := by decide
  have hdescent : baseEnd_542562 < baseStart_542562 := by decide
  rcases family_descends (prefixWord ++ tailWord_542562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542593 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_542593 : Nat := 118140960795 + 542593 * 2 ^ 59
def prefixEnd_542593 : Nat := 4983230072969 + 3 ^ 40 * 542593 * 2
def baseEnd_542593 : Nat := 247654230013422965415259

theorem tailTrace_542593 : CollatzResearch.WordTrace tailWord_542593 prefixEnd_542593 247654230013422965415259 := by
  unfold tailWord_542593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19789992523285703351872433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13193328348857135567914955 19789992523285703351872433)
  ·
    refine ⟨14842494392464277513904325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19789992523285703351872433 14842494392464277513904325)
    ·
      refine ⟨2782967698587052033857061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14842494392464277513904325 2782967698587052033857061)
      ·
        refine ⟨521806443485072256348199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2782967698587052033857061 521806443485072256348199)
        ·
          refine ⟨782709665227608384522299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521806443485072256348199 782709665227608384522299)
          ·
            refine ⟨1174064497841412576783449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782709665227608384522299 1174064497841412576783449)
            ·
              refine ⟨880548373381059432587587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174064497841412576783449 880548373381059432587587)
              ·
                refine ⟨1320822560071589148881381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880548373381059432587587 1320822560071589148881381)
                ·
                  refine ⟨247654230013422965415259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320822560071589148881381 247654230013422965415259)
                  ·
                    rfl

theorem cell20_542593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_542593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542593 prefixEnd_542593 := by exact prefixLift 542593
  have htrace : WordTrace (prefixWord ++ tailWord_542593) baseStart_542593 baseEnd_542593 := by
    simpa [prefixWord, tailWord_542593, baseEnd_542593] using wordTrace_append hprefix tailTrace_542593
  have hstable : (prefixWord ++ tailWord_542593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542593).length < 2 ^ (prefixWord ++ tailWord_542593).sum := by decide
  have hdescent : baseEnd_542593 < baseStart_542593 := by decide
  rcases family_descends (prefixWord ++ tailWord_542593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542597 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_542597 : Nat := 118140960795 + 542597 * 2 ^ 59
def prefixEnd_542597 : Nat := 4983230072969 + 3 ^ 40 * 542597 * 2
def baseEnd_542597 : Nat := 247656055722416729281909

theorem tailTrace_542597 : CollatzResearch.WordTrace tailWord_542597 prefixEnd_542597 247656055722416729281909 := by
  unfold tailWord_542597
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790138415271212035018045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13193425610180808023345363 19790138415271212035018045)
  ·
    refine ⟨7421301905726704513131767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19790138415271212035018045 7421301905726704513131767)
    ·
      refine ⟨11131952858590056769697651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7421301905726704513131767 11131952858590056769697651)
      ·
        refine ⟨16697929287885085154546477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11131952858590056769697651 16697929287885085154546477)
        ·
          refine ⟨6261723482956906932954929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16697929287885085154546477 6261723482956906932954929)
          ·
            refine ⟨4696292612217680199716197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6261723482956906932954929 4696292612217680199716197)
            ·
              refine ⟨880554864790815037446787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4696292612217680199716197 880554864790815037446787)
              ·
                refine ⟨1320832297186222556170181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880554864790815037446787 1320832297186222556170181)
                ·
                  refine ⟨247656055722416729281909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320832297186222556170181 247656055722416729281909)
                  ·
                    rfl

theorem cell20_542597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_542597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542597 prefixEnd_542597 := by exact prefixLift 542597
  have htrace : WordTrace (prefixWord ++ tailWord_542597) baseStart_542597 baseEnd_542597 := by
    simpa [prefixWord, tailWord_542597, baseEnd_542597] using wordTrace_append hprefix tailTrace_542597
  have hstable : (prefixWord ++ tailWord_542597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542597).length < 2 ^ (prefixWord ++ tailWord_542597).sum := by decide
  have hdescent : baseEnd_542597 < baseStart_542597 := by decide
  rcases family_descends (prefixWord ++ tailWord_542597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542621 : List Nat := [1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_542621 : Nat := 118140960795 + 542621 * 2 ^ 59
def prefixEnd_542621 : Nat := 4983230072969 + 3 ^ 40 * 542621 * 2
def baseEnd_542621 : Nat := 82555669992126437493937

theorem tailTrace_542621 : CollatzResearch.WordTrace tailWord_542621 prefixEnd_542621 82555669992126437493937 := by
  unfold tailWord_542621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791013767184264133891717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13194009178122842755927811 19791013767184264133891717)
  ·
    refine ⟨3710815081347049525104697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19791013767184264133891717 3710815081347049525104697)
    ·
      refine ⟨2783111311010287143828523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3710815081347049525104697 2783111311010287143828523)
      ·
        refine ⟨4174666966515430715742785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783111311010287143828523 4174666966515430715742785)
        ·
          refine ⟨3131000224886573036807089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4174666966515430715742785 3131000224886573036807089)
          ·
            refine ⟨2348250168664929777605317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131000224886573036807089 2348250168664929777605317)
            ·
              refine ⟨440296906624674333300997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2348250168664929777605317 440296906624674333300997)
              ·
                refine ⟨82555669992126437493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440296906624674333300997 82555669992126437493937)
                ·
                  rfl

theorem cell20_542621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_542621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542621 prefixEnd_542621 := by exact prefixLift 542621
  have htrace : WordTrace (prefixWord ++ tailWord_542621) baseStart_542621 baseEnd_542621 := by
    simpa [prefixWord, tailWord_542621, baseEnd_542621] using wordTrace_append hprefix tailTrace_542621
  have hstable : (prefixWord ++ tailWord_542621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542621).length < 2 ^ (prefixWord ++ tailWord_542621).sum := by decide
  have hdescent : baseEnd_542621 < baseStart_542621 := by decide
  rcases family_descends (prefixWord ++ tailWord_542621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542631 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 2]
def baseStart_542631 : Nat := 118140960795 + 542631 * 2 ^ 59
def prefixEnd_542631 : Nat := 4983230072969 + 3 ^ 40 * 542631 * 2
def baseEnd_542631 : Nat := 247671574248863722148437

theorem tailTrace_542631 : CollatzResearch.WordTrace tailWord_542631 prefixEnd_542631 247671574248863722148437 := by
  unfold tailWord_542631
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791378497148035841755747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13194252331432023894503831 19791378497148035841755747)
  ·
    refine ⟨29687067745722053762633621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19791378497148035841755747 29687067745722053762633621)
    ·
      refine ⟨1391581300580721270123451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29687067745722053762633621 1391581300580721270123451)
      ·
        refine ⟨2087371950871081905185177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391581300580721270123451 2087371950871081905185177)
        ·
          refine ⟨1565528963153311428888883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087371950871081905185177 1565528963153311428888883)
          ·
            refine ⟨2348293444729967143333325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565528963153311428888883 2348293444729967143333325)
            ·
              refine ⟨880610041773737678749997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2348293444729967143333325 880610041773737678749997)
              ·
                refine ⟨330228765665151629531249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880610041773737678749997 330228765665151629531249)
                ·
                  refine ⟨247671574248863722148437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330228765665151629531249 247671574248863722148437)
                  ·
                    rfl

theorem cell20_542631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2].length) (baseStart_542631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542631 prefixEnd_542631 := by exact prefixLift 542631
  have htrace : WordTrace (prefixWord ++ tailWord_542631) baseStart_542631 baseEnd_542631 := by
    simpa [prefixWord, tailWord_542631, baseEnd_542631] using wordTrace_append hprefix tailTrace_542631
  have hstable : (prefixWord ++ tailWord_542631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542631).length < 2 ^ (prefixWord ++ tailWord_542631).sum := by decide
  have hdescent : baseEnd_542631 < baseStart_542631 := by decide
  rcases family_descends (prefixWord ++ tailWord_542631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542649 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_542649 : Nat := 118140960795 + 542649 * 2 ^ 59
def prefixEnd_542649 : Nat := 4983230072969 + 3 ^ 40 * 542649 * 2
def baseEnd_542649 : Nat := 247679789939335659548363

theorem tailTrace_542649 : CollatzResearch.WordTrace tailWord_542649 prefixEnd_542649 247679789939335659548363 := by
  unfold tailWord_542649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19792035011082824915911001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13194690007388549943940667 19792035011082824915911001)
  ·
    refine ⟨14844026258312118686933251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19792035011082824915911001 14844026258312118686933251)
    ·
      refine ⟨22266039387468178030399877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14844026258312118686933251 22266039387468178030399877)
      ·
        refine ⟨4174882385150283380699977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22266039387468178030399877 4174882385150283380699977)
        ·
          refine ⟨3131161788862712535524983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4174882385150283380699977 3131161788862712535524983)
          ·
            refine ⟨4696742683294068803287475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131161788862712535524983 4696742683294068803287475)
            ·
              refine ⟨7045114024941103204931213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696742683294068803287475 7045114024941103204931213)
              ·
                refine ⟨2641917759352913701849205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7045114024941103204931213 2641917759352913701849205)
                ·
                  refine ⟨247679789939335659548363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641917759352913701849205 247679789939335659548363)
                  ·
                    rfl

theorem cell20_542649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_542649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542649 prefixEnd_542649 := by exact prefixLift 542649
  have htrace : WordTrace (prefixWord ++ tailWord_542649) baseStart_542649 baseEnd_542649 := by
    simpa [prefixWord, tailWord_542649, baseEnd_542649] using wordTrace_append hprefix tailTrace_542649
  have hstable : (prefixWord ++ tailWord_542649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542649).length < 2 ^ (prefixWord ++ tailWord_542649).sum := by decide
  have hdescent : baseEnd_542649 < baseStart_542649 := by decide
  rcases family_descends (prefixWord ++ tailWord_542649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542739 : List Nat := [1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_542739 : Nat := 118140960795 + 542739 * 2 ^ 59
def prefixEnd_542739 : Nat := 4983230072969 + 3 ^ 40 * 542739 * 2
def baseEnd_542739 : Nat := 82573622797231782182665

theorem tailTrace_542739 : CollatzResearch.WordTrace tailWord_542739 prefixEnd_542739 82573622797231782182665 := by
  unfold tailWord_542739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795317580756770286687271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13196878387171180191124847 19795317580756770286687271)
  ·
    refine ⟨29692976371135155430030907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19795317580756770286687271 29692976371135155430030907)
    ·
      refine ⟨44539464556702733145046361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29692976371135155430030907 44539464556702733145046361)
      ·
        refine ⟨33404598417527049858784771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44539464556702733145046361 33404598417527049858784771)
        ·
          refine ⟨50106897626290574788177157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33404598417527049858784771 50106897626290574788177157)
          ·
            refine ⟨9395043304929482772783217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50106897626290574788177157 9395043304929482772783217)
            ·
              refine ⟨7046282478697112079587413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395043304929482772783217 7046282478697112079587413)
              ·
                refine ⟨82573622797231782182665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7046282478697112079587413 82573622797231782182665)
                ·
                  rfl

theorem cell20_542739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_542739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542739 prefixEnd_542739 := by exact prefixLift 542739
  have htrace : WordTrace (prefixWord ++ tailWord_542739) baseStart_542739 baseEnd_542739 := by
    simpa [prefixWord, tailWord_542739, baseEnd_542739] using wordTrace_append hprefix tailTrace_542739
  have hstable : (prefixWord ++ tailWord_542739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542739).length < 2 ^ (prefixWord ++ tailWord_542739).sum := by decide
  have hdescent : baseEnd_542739 < baseStart_542739 := by decide
  rcases family_descends (prefixWord ++ tailWord_542739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542759 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_542759 : Nat := 118140960795 + 542759 * 2 ^ 59
def prefixEnd_542759 : Nat := 4983230072969 + 3 ^ 40 * 542759 * 2
def baseEnd_542759 : Nat := 247729996936664165881247

theorem tailTrace_542759 : CollatzResearch.WordTrace tailWord_542759 prefixEnd_542759 247729996936664165881247 := by
  unfold tailWord_542759
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796047040684313702415331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197364693789542468276887 19796047040684313702415331)
  ·
    refine ⟨29694070561026470553622997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19796047040684313702415331 29694070561026470553622997)
    ·
      refine ⟨695954778774057903600539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29694070561026470553622997 695954778774057903600539)
      ·
        refine ⟨1043932168161086855400809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695954778774057903600539 1043932168161086855400809)
        ·
          refine ⟨782949126120815141550607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043932168161086855400809 782949126120815141550607)
          ·
            refine ⟨1174423689181222712325911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782949126120815141550607 1174423689181222712325911)
            ·
              refine ⟨1761635533771834068488867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174423689181222712325911 1761635533771834068488867)
              ·
                refine ⟨2642453300657751102733301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761635533771834068488867 2642453300657751102733301)
                ·
                  refine ⟨247729996936664165881247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642453300657751102733301 247729996936664165881247)
                  ·
                    rfl

theorem cell20_542759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_542759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542759 prefixEnd_542759 := by exact prefixLift 542759
  have htrace : WordTrace (prefixWord ++ tailWord_542759) baseStart_542759 baseEnd_542759 := by
    simpa [prefixWord, tailWord_542759, baseEnd_542759] using wordTrace_append hprefix tailTrace_542759
  have hstable : (prefixWord ++ tailWord_542759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542759).length < 2 ^ (prefixWord ++ tailWord_542759).sum := by decide
  have hdescent : baseEnd_542759 < baseStart_542759 := by decide
  rcases family_descends (prefixWord ++ tailWord_542759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_542763 : Nat := 118140960795 + 542763 * 2 ^ 59
def prefixEnd_542763 : Nat := 4983230072969 + 3 ^ 40 * 542763 * 2
def baseEnd_542763 : Nat := 247731822645657929747897

theorem tailTrace_542763 : CollatzResearch.WordTrace tailWord_542763 prefixEnd_542763 247731822645657929747897 := by
  unfold tailWord_542763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796192932669822385560943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13197461955113214923707295 19796192932669822385560943)
  ·
    refine ⟨29694289399004733578341415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19796192932669822385560943 29694289399004733578341415)
    ·
      refine ⟨44541434098507100367512123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694289399004733578341415 44541434098507100367512123)
      ·
        refine ⟨66812151147760650551268185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44541434098507100367512123 66812151147760650551268185)
        ·
          refine ⟨50109113360820487913451139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66812151147760650551268185 50109113360820487913451139)
          ·
            refine ⟨75163670041230731870176709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50109113360820487913451139 75163670041230731870176709)
            ·
              refine ⟨14093188132730762225658133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75163670041230731870176709 14093188132730762225658133)
              ·
                refine ⟨660618193721754479327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14093188132730762225658133 660618193721754479327725)
                ·
                  refine ⟨247731822645657929747897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660618193721754479327725 247731822645657929747897)
                  ·
                    rfl

theorem cell20_542763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_542763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542763 prefixEnd_542763 := by exact prefixLift 542763
  have htrace : WordTrace (prefixWord ++ tailWord_542763) baseStart_542763 baseEnd_542763 := by
    simpa [prefixWord, tailWord_542763, baseEnd_542763] using wordTrace_append hprefix tailTrace_542763
  have hstable : (prefixWord ++ tailWord_542763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542763).length < 2 ^ (prefixWord ++ tailWord_542763).sum := by decide
  have hdescent : baseEnd_542763 < baseStart_542763 := by decide
  rcases family_descends (prefixWord ++ tailWord_542763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542766 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_542766 : Nat := 118140960795 + 542766 * 2 ^ 59
def prefixEnd_542766 : Nat := 4983230072969 + 3 ^ 40 * 542766 * 2
def baseEnd_542766 : Nat := 247733191927403252647885

theorem tailTrace_542766 : CollatzResearch.WordTrace tailWord_542766 prefixEnd_542766 247733191927403252647885 := by
  unfold tailWord_542766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474537793957369237240019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13197534901105969265280101 2474537793957369237240019)
  ·
    refine ⟨3711806690936053855860029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2474537793957369237240019 3711806690936053855860029)
    ·
      refine ⟨1391927509101020195947511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3711806690936053855860029 1391927509101020195947511)
      ·
        refine ⟨2087891263651530293921267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391927509101020195947511 2087891263651530293921267)
        ·
          refine ⟨3131836895477295440881901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087891263651530293921267 3131836895477295440881901)
          ·
            refine ⟨1174438835803985790330713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3131836895477295440881901 1174438835803985790330713)
            ·
              refine ⟨880829126852989342748035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174438835803985790330713 880829126852989342748035)
              ·
                refine ⟨1321243690279484014122053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880829126852989342748035 1321243690279484014122053)
                ·
                  refine ⟨247733191927403252647885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321243690279484014122053 247733191927403252647885)
                  ·
                    rfl

theorem cell20_542766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_542766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542766 prefixEnd_542766 := by exact prefixLift 542766
  have htrace : WordTrace (prefixWord ++ tailWord_542766) baseStart_542766 baseEnd_542766 := by
    simpa [prefixWord, tailWord_542766, baseEnd_542766] using wordTrace_append hprefix tailTrace_542766
  have hstable : (prefixWord ++ tailWord_542766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542766).length < 2 ^ (prefixWord ++ tailWord_542766).sum := by decide
  have hdescent : baseEnd_542766 < baseStart_542766 := by decide
  rcases family_descends (prefixWord ++ tailWord_542766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542821 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 2]
def baseStart_542821 : Nat := 118140960795 + 542821 * 2 ^ 59
def prefixEnd_542821 : Nat := 4983230072969 + 3 ^ 40 * 542821 * 2
def baseEnd_542821 : Nat := 247758295426067505814327

theorem tailTrace_542821 : CollatzResearch.WordTrace tailWord_542821 prefixEnd_542821 247758295426067505814327 := by
  unfold tailWord_542821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19798308366459698291172317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13198872244306465527448211 19798308366459698291172317)
  ·
    refine ⟨7424365637422386859189619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19798308366459698291172317 7424365637422386859189619)
    ·
      refine ⟨11136548456133580288784429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7424365637422386859189619 11136548456133580288784429)
      ·
        refine ⟨4176205671050092608294161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11136548456133580288784429 4176205671050092608294161)
        ·
          refine ⟨3132154253287569456220621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176205671050092608294161 3132154253287569456220621)
          ·
            refine ⟨1174557844982838546082733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3132154253287569456220621 1174557844982838546082733)
            ·
              refine ⟨440459191868564454781025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174557844982838546082733 440459191868564454781025)
              ·
                refine ⟨330344393901423341085769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440459191868564454781025 330344393901423341085769)
                ·
                  refine ⟨247758295426067505814327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330344393901423341085769 247758295426067505814327)
                  ·
                    rfl

theorem cell20_542821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_542821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542821 prefixEnd_542821 := by exact prefixLift 542821
  have htrace : WordTrace (prefixWord ++ tailWord_542821) baseStart_542821 baseEnd_542821 := by
    simpa [prefixWord, tailWord_542821, baseEnd_542821] using wordTrace_append hprefix tailTrace_542821
  have hstable : (prefixWord ++ tailWord_542821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542821).length < 2 ^ (prefixWord ++ tailWord_542821).sum := by decide
  have hdescent : baseEnd_542821 < baseStart_542821 := by decide
  rcases family_descends (prefixWord ++ tailWord_542821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542832 : List Nat := [2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_542832 : Nat := 118140960795 + 542832 * 2 ^ 59
def prefixEnd_542832 : Nat := 4983230072969 + 3 ^ 40 * 542832 * 2
def baseEnd_542832 : Nat := 82587772041933452149205

theorem tailTrace_542832 : CollatzResearch.WordTrace tailWord_542832 prefixEnd_542832 82587772041933452149205 := by
  unfold tailWord_542832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899354784709923584911375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13199139712946564779881833 9899354784709923584911375)
  ·
    refine ⟨14849032177064885377367063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9899354784709923584911375 14849032177064885377367063)
    ·
      refine ⟨22273548265597328066050595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14849032177064885377367063 22273548265597328066050595)
      ·
        refine ⟨33410322398395992099075893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22273548265597328066050595 33410322398395992099075893)
        ·
          refine ⟨3132217724849624259288365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33410322398395992099075893 3132217724849624259288365)
          ·
            refine ⟨1174581646818609097233137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3132217724849624259288365 1174581646818609097233137)
            ·
              refine ⟨880936235113956822924853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174581646818609097233137 880936235113956822924853)
              ·
                refine ⟨82587772041933452149205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 880936235113956822924853 82587772041933452149205)
                ·
                  rfl

theorem cell20_542832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_542832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542832 prefixEnd_542832 := by exact prefixLift 542832
  have htrace : WordTrace (prefixWord ++ tailWord_542832) baseStart_542832 baseEnd_542832 := by
    simpa [prefixWord, tailWord_542832, baseEnd_542832] using wordTrace_append hprefix tailTrace_542832
  have hstable : (prefixWord ++ tailWord_542832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542832).length < 2 ^ (prefixWord ++ tailWord_542832).sum := by decide
  have hdescent : baseEnd_542832 < baseStart_542832 := by decide
  rcases family_descends (prefixWord ++ tailWord_542832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542880 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_542880 : Nat := 118140960795 + 542880 * 2 ^ 59
def prefixEnd_542880 : Nat := 4983230072969 + 3 ^ 40 * 542880 * 2
def baseEnd_542880 : Nat := 247785224633725522847419

theorem tailTrace_542880 : CollatzResearch.WordTrace tailWord_542880 prefixEnd_542880 247785224633725522847419 := by
  unfold tailWord_542880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900230136622975683785047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13200306848830634245046729 9900230136622975683785047)
  ·
    refine ⟨14850345204934463525677571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9900230136622975683785047 14850345204934463525677571)
    ·
      refine ⟨22275517807401695288516357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14850345204934463525677571 22275517807401695288516357)
      ·
        refine ⟨4176659588887817866596817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22275517807401695288516357 4176659588887817866596817)
        ·
          refine ⟨3132494691665863399947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176659588887817866596817 3132494691665863399947613)
          ·
            refine ⟨1174685509374698774980355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3132494691665863399947613 1174685509374698774980355)
            ·
              refine ⟨1762028264062048162470533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174685509374698774980355 1762028264062048162470533)
              ·
                refine ⟨330380299511634030463225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1762028264062048162470533 330380299511634030463225)
                ·
                  refine ⟨247785224633725522847419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330380299511634030463225 247785224633725522847419)
                  ·
                    rfl

theorem cell20_542880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_542880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542880 prefixEnd_542880 := by exact prefixLift 542880
  have htrace : WordTrace (prefixWord ++ tailWord_542880) baseStart_542880 baseEnd_542880 := by
    simpa [prefixWord, tailWord_542880, baseEnd_542880] using wordTrace_append hprefix tailTrace_542880
  have hstable : (prefixWord ++ tailWord_542880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542880).length < 2 ^ (prefixWord ++ tailWord_542880).sum := by decide
  have hdescent : baseEnd_542880 < baseStart_542880 := by decide
  rcases family_descends (prefixWord ++ tailWord_542880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542900 : List Nat := [2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_542900 : Nat := 118140960795 + 542900 * 2 ^ 59
def prefixEnd_542900 : Nat := 4983230072969 + 3 ^ 40 * 542900 * 2
def baseEnd_542900 : Nat := 82598117726231447393557

theorem tailTrace_542900 : CollatzResearch.WordTrace tailWord_542900 prefixEnd_542900 82598117726231447393557 := by
  unfold tailWord_542900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900594866586747391649077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13200793155448996522198769 9900594866586747391649077)
  ·
    refine ⟨928180768742507567967101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9900594866586747391649077 928180768742507567967101)
    ·
      refine ⟨348067788278440337987663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 928180768742507567967101 348067788278440337987663)
      ·
        refine ⟨522101682417660506981495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348067788278440337987663 522101682417660506981495)
        ·
          refine ⟨783152523626490760472243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522101682417660506981495 783152523626490760472243)
          ·
            refine ⟨1174728785439736140708365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783152523626490760472243 1174728785439736140708365)
            ·
              refine ⟨440523294539901052765637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174728785439736140708365 440523294539901052765637)
              ·
                refine ⟨82598117726231447393557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440523294539901052765637 82598117726231447393557)
                ·
                  rfl

theorem cell20_542900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_542900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542900 prefixEnd_542900 := by exact prefixLift 542900
  have htrace : WordTrace (prefixWord ++ tailWord_542900) baseStart_542900 baseEnd_542900 := by
    simpa [prefixWord, tailWord_542900, baseEnd_542900] using wordTrace_append hprefix tailTrace_542900
  have hstable : (prefixWord ++ tailWord_542900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542900).length < 2 ^ (prefixWord ++ tailWord_542900).sum := by decide
  have hdescent : baseEnd_542900 < baseStart_542900 := by decide
  rcases family_descends (prefixWord ++ tailWord_542900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542914 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_542914 : Nat := 118140960795 + 542914 * 2 ^ 59
def prefixEnd_542914 : Nat := 4983230072969 + 3 ^ 40 * 542914 * 2
def baseEnd_542914 : Nat := 247800743160172515713947

theorem tailTrace_542914 : CollatzResearch.WordTrace tailWord_542914 prefixEnd_542914 247800743160172515713947 := by
  unfold tailWord_542914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950425088780693793576949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13201133570081850116205197 4950425088780693793576949)
  ·
    refine ⟨464102352073190043147839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4950425088780693793576949 464102352073190043147839)
    ·
      refine ⟨696153528109785064721759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464102352073190043147839 696153528109785064721759)
      ·
        refine ⟨1044230292164677597082639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696153528109785064721759 1044230292164677597082639)
        ·
          refine ⟨1566345438247016395623959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044230292164677597082639 1566345438247016395623959)
          ·
            refine ⟨2349518157370524593435939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566345438247016395623959 2349518157370524593435939)
            ·
              refine ⟨3524277236055786890153909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349518157370524593435939 3524277236055786890153909)
              ·
                refine ⟨330400990880230020951929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3524277236055786890153909 330400990880230020951929)
                ·
                  refine ⟨247800743160172515713947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330400990880230020951929 247800743160172515713947)
                  ·
                    rfl

theorem cell20_542914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_542914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542914 prefixEnd_542914 := by exact prefixLift 542914
  have htrace : WordTrace (prefixWord ++ tailWord_542914) baseStart_542914 baseEnd_542914 := by
    simpa [prefixWord, tailWord_542914, baseEnd_542914] using wordTrace_append hprefix tailTrace_542914
  have hstable : (prefixWord ++ tailWord_542914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542914).length < 2 ^ (prefixWord ++ tailWord_542914).sum := by decide
  have hdescent : baseEnd_542914 < baseStart_542914 := by decide
  rcases family_descends (prefixWord ++ tailWord_542914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542922 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_542922 : Nat := 118140960795 + 542922 * 2 ^ 59
def prefixEnd_542922 : Nat := 4983230072969 + 3 ^ 40 * 542922 * 2
def baseEnd_542922 : Nat := 247804394578160043447247

theorem tailTrace_542922 : CollatzResearch.WordTrace tailWord_542922 prefixEnd_542922 247804394578160043447247 := by
  unfold tailWord_542922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950498034773448135149755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13201328092729195027066013 4950498034773448135149755)
  ·
    refine ⟨7425747052160172202724633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950498034773448135149755 7425747052160172202724633)
    ·
      refine ⟨5569310289120129152043475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7425747052160172202724633 5569310289120129152043475)
      ·
        refine ⟨8353965433680193728065213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569310289120129152043475 8353965433680193728065213)
        ·
          refine ⟨3132737037630072648024455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8353965433680193728065213 3132737037630072648024455)
          ·
            refine ⟨4699105556445108972036683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132737037630072648024455 4699105556445108972036683)
            ·
              refine ⟨7048658334667663458055025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699105556445108972036683 7048658334667663458055025)
              ·
                refine ⟨5286493751000747593541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7048658334667663458055025 5286493751000747593541269)
                ·
                  refine ⟨247804394578160043447247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5286493751000747593541269 247804394578160043447247)
                  ·
                    rfl

theorem cell20_542922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_542922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542922 prefixEnd_542922 := by exact prefixLift 542922
  have htrace : WordTrace (prefixWord ++ tailWord_542922) baseStart_542922 baseEnd_542922 := by
    simpa [prefixWord, tailWord_542922, baseEnd_542922] using wordTrace_append hprefix tailTrace_542922
  have hstable : (prefixWord ++ tailWord_542922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542922).length < 2 ^ (prefixWord ++ tailWord_542922).sum := by decide
  have hdescent : baseEnd_542922 < baseStart_542922 := by decide
  rcases family_descends (prefixWord ++ tailWord_542922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542949 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_542949 : Nat := 118140960795 + 542949 * 2 ^ 59
def prefixEnd_542949 : Nat := 4983230072969 + 3 ^ 40 * 542949 * 2
def baseEnd_542949 : Nat := 247816718113867949547137

theorem tailTrace_542949 : CollatzResearch.WordTrace tailWord_542949 prefixEnd_542949 247816718113867949547137 := by
  unfold tailWord_542949
  simp only [CollatzResearch.WordTrace]
  refine ⟨19802976909995976151831901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13201984606663984101221267 19802976909995976151831901)
  ·
    refine ⟨7426116341248491056936963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19802976909995976151831901 7426116341248491056936963)
    ·
      refine ⟨11139174511872736585405445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7426116341248491056936963 11139174511872736585405445)
      ·
        refine ⟨2088595220976138109763521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11139174511872736585405445 2088595220976138109763521)
        ·
          refine ⟨1566446415732103582322641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088595220976138109763521 1566446415732103582322641)
          ·
            refine ⟨1174834811799077686741981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566446415732103582322641 1174834811799077686741981)
            ·
              refine ⟨440563054424654132528243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174834811799077686741981 440563054424654132528243)
              ·
                refine ⟨660844581636981198792365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440563054424654132528243 660844581636981198792365)
                ·
                  refine ⟨247816718113867949547137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660844581636981198792365 247816718113867949547137)
                  ·
                    rfl

theorem cell20_542949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_542949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542949 prefixEnd_542949 := by exact prefixLift 542949
  have htrace : WordTrace (prefixWord ++ tailWord_542949) baseStart_542949 baseEnd_542949 := by
    simpa [prefixWord, tailWord_542949, baseEnd_542949] using wordTrace_append hprefix tailTrace_542949
  have hstable : (prefixWord ++ tailWord_542949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542949).length < 2 ^ (prefixWord ++ tailWord_542949).sum := by decide
  have hdescent : baseEnd_542949 < baseStart_542949 := by decide
  rcases family_descends (prefixWord ++ tailWord_542949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542984 : List Nat := [2, 1, 3, 2, 3, 3, 6]
def baseStart_542984 : Nat := 118140960795 + 542984 * 2 ^ 59
def prefixEnd_542984 : Nat := 4983230072969 + 3 ^ 40 * 542984 * 2
def baseEnd_542984 : Nat := 27536965896395931486703

theorem tailTrace_542984 : CollatzResearch.WordTrace tailWord_542984 prefixEnd_542984 27536965896395931486703 := by
  unfold tailWord_542984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902126732434588564678003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13202835643246118086237337 9902126732434588564678003)
  ·
    refine ⟨14853190098651882847017005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9902126732434588564678003 14853190098651882847017005)
    ·
      refine ⟨5569946286994456067631377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14853190098651882847017005 5569946286994456067631377)
      ·
        refine ⟨4177459715245842050723533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5569946286994456067631377 4177459715245842050723533)
        ·
          refine ⟨1566547393217190769021325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4177459715245842050723533 1566547393217190769021325)
          ·
            refine ⟨587455272456446538382997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1566547393217190769021325 587455272456446538382997)
            ·
              refine ⟨27536965896395931486703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 587455272456446538382997 27536965896395931486703)
              ·
                rfl

theorem cell20_542984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_542984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542984 prefixEnd_542984 := by exact prefixLift 542984
  have htrace : WordTrace (prefixWord ++ tailWord_542984) baseStart_542984 baseEnd_542984 := by
    simpa [prefixWord, tailWord_542984, baseEnd_542984] using wordTrace_append hprefix tailTrace_542984
  have hstable : (prefixWord ++ tailWord_542984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542984).length < 2 ^ (prefixWord ++ tailWord_542984).sum := by decide
  have hdescent : baseEnd_542984 < baseStart_542984 := by decide
  rcases family_descends (prefixWord ++ tailWord_542984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543008 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_543008 : Nat := 118140960795 + 543008 * 2 ^ 59
def prefixEnd_543008 : Nat := 4983230072969 + 3 ^ 40 * 543008 * 2
def baseEnd_543008 : Nat := 247843647321525966580229

theorem tailTrace_543008 : CollatzResearch.WordTrace tailWord_543008 prefixEnd_543008 247843647321525966580229 := by
  unfold tailWord_543008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902564408391114614114839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13203419211188152818819785 9902564408391114614114839)
  ·
    refine ⟨14853846612586671921172259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9902564408391114614114839 14853846612586671921172259)
    ·
      refine ⟨22280769918880007881758389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14853846612586671921172259 22280769918880007881758389)
      ·
        refine ⟨2088822179895000738914849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22280769918880007881758389 2088822179895000738914849)
        ·
          refine ⟨1566616634921250554186137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088822179895000738914849 1566616634921250554186137)
          ·
            refine ⟨1174962476190937915639603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566616634921250554186137 1174962476190937915639603)
            ·
              refine ⟨1762443714286406873459405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174962476190937915639603 1762443714286406873459405)
              ·
                refine ⟨660916392857402577547277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762443714286406873459405 660916392857402577547277)
                ·
                  refine ⟨247843647321525966580229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660916392857402577547277 247843647321525966580229)
                  ·
                    rfl

theorem cell20_543008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_543008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543008 prefixEnd_543008 := by exact prefixLift 543008
  have htrace : WordTrace (prefixWord ++ tailWord_543008) baseStart_543008 baseEnd_543008 := by
    simpa [prefixWord, tailWord_543008, baseEnd_543008] using wordTrace_append hprefix tailTrace_543008
  have hstable : (prefixWord ++ tailWord_543008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543008).length < 2 ^ (prefixWord ++ tailWord_543008).sum := by decide
  have hdescent : baseEnd_543008 < baseStart_543008 := by decide
  rcases family_descends (prefixWord ++ tailWord_543008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543060 : List Nat := [2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_543060 : Nat := 118140960795 + 543060 * 2 ^ 59
def prefixEnd_543060 : Nat := 4983230072969 + 3 ^ 40 * 543060 * 2
def baseEnd_543060 : Nat := 82622460512814965615561

theorem tailTrace_543060 : CollatzResearch.WordTrace tailWord_543060 prefixEnd_543060 82622460512814965615561 := by
  unfold tailWord_543060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903512706296921054561317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13204683608395894739415089 9903512706296921054561317)
  ·
    refine ⟨1856908632430672697730247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9903512706296921054561317 1856908632430672697730247)
    ·
      refine ⟨2785362948646009046595371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856908632430672697730247 2785362948646009046595371)
      ·
        refine ⟨4178044422969013569893057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785362948646009046595371 4178044422969013569893057)
        ·
          refine ⟨3133533317226760177419793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4178044422969013569893057 3133533317226760177419793)
          ·
            refine ⟨2350149987920070133064845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133533317226760177419793 2350149987920070133064845)
            ·
              refine ⟨881306245470026299899317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2350149987920070133064845 881306245470026299899317)
              ·
                refine ⟨82622460512814965615561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 881306245470026299899317 82622460512814965615561)
                ·
                  rfl

theorem cell20_543060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_543060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543060 prefixEnd_543060 := by exact prefixLift 543060
  have htrace : WordTrace (prefixWord ++ tailWord_543060) baseStart_543060 baseEnd_543060 := by
    simpa [prefixWord, tailWord_543060, baseEnd_543060] using wordTrace_append hprefix tailTrace_543060
  have hstable : (prefixWord ++ tailWord_543060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543060).length < 2 ^ (prefixWord ++ tailWord_543060).sum := by decide
  have hdescent : baseEnd_543060 < baseStart_543060 := by decide
  rcases family_descends (prefixWord ++ tailWord_543060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543136 : List Nat := [2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_543136 : Nat := 118140960795 + 543136 * 2 ^ 59
def prefixEnd_543136 : Nat := 4983230072969 + 3 ^ 40 * 543136 * 2
def baseEnd_543136 : Nat := 82634023336442136771013

theorem tailTrace_543136 : CollatzResearch.WordTrace tailWord_543136 prefixEnd_543136 82634023336442136771013 := by
  unfold tailWord_543136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9904898680159253544444631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13206531573545671392592841 9904898680159253544444631)
  ·
    refine ⟨14857348020238880316666947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9904898680159253544444631 14857348020238880316666947)
    ·
      refine ⟨22286022030358320475000421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14857348020238880316666947 22286022030358320475000421)
      ·
        refine ⟨4178629130692185089062579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22286022030358320475000421 4178629130692185089062579)
        ·
          refine ⟨6267943696038277633593869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178629130692185089062579 6267943696038277633593869)
          ·
            refine ⟨2350478886014354112597701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6267943696038277633593869 2350478886014354112597701)
            ·
              refine ⟨440714791127691396112069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2350478886014354112597701 440714791127691396112069)
              ·
                refine ⟨82634023336442136771013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440714791127691396112069 82634023336442136771013)
                ·
                  rfl

theorem cell20_543136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_543136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543136 prefixEnd_543136 := by exact prefixLift 543136
  have htrace : WordTrace (prefixWord ++ tailWord_543136) baseStart_543136 baseEnd_543136 := by
    simpa [prefixWord, tailWord_543136, baseEnd_543136] using wordTrace_append hprefix tailTrace_543136
  have hstable : (prefixWord ++ tailWord_543136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543136).length < 2 ^ (prefixWord ++ tailWord_543136).sum := by decide
  have hdescent : baseEnd_543136 < baseStart_543136 := by decide
  rcases family_descends (prefixWord ++ tailWord_543136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543143 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_543143 : Nat := 118140960795 + 543143 * 2 ^ 59
def prefixEnd_543143 : Nat := 4983230072969 + 3 ^ 40 * 543143 * 2
def baseEnd_543143 : Nat := 247905265000065497079677

theorem tailTrace_543143 : CollatzResearch.WordTrace tailWord_543143 prefixEnd_543143 247905265000065497079677 := by
  unfold tailWord_543143
  simp only [CollatzResearch.WordTrace]
  refine ⟨19810052671293147284394083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13206701780862098189596055 19810052671293147284394083)
  ·
    refine ⟨29715079006939720926591125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19810052671293147284394083 29715079006939720926591125)
    ·
      refine ⟨1392894328450299418433959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29715079006939720926591125 1392894328450299418433959)
      ·
        refine ⟨2089341492675449127650939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392894328450299418433959 2089341492675449127650939)
        ·
          refine ⟨3134012239013173691476409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089341492675449127650939 3134012239013173691476409)
          ·
            refine ⟨2350509179259880268607307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134012239013173691476409 2350509179259880268607307)
            ·
              refine ⟨3525763768889820402910961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350509179259880268607307 3525763768889820402910961)
              ·
                refine ⟨2644322826667365302183221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525763768889820402910961 2644322826667365302183221)
                ·
                  refine ⟨247905265000065497079677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644322826667365302183221 247905265000065497079677)
                  ·
                    rfl

theorem cell20_543143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_543143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543143 prefixEnd_543143 := by exact prefixLift 543143
  have htrace : WordTrace (prefixWord ++ tailWord_543143) baseStart_543143 baseEnd_543143 := by
    simpa [prefixWord, tailWord_543143, baseEnd_543143] using wordTrace_append hprefix tailTrace_543143
  have hstable : (prefixWord ++ tailWord_543143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543143).length < 2 ^ (prefixWord ++ tailWord_543143).sum := by decide
  have hdescent : baseEnd_543143 < baseStart_543143 := by decide
  rcases family_descends (prefixWord ++ tailWord_543143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543209 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_543209 : Nat := 118140960795 + 543209 * 2 ^ 59
def prefixEnd_543209 : Nat := 4983230072969 + 3 ^ 40 * 543209 * 2
def baseEnd_543209 : Nat := 247935389198462600879407

theorem tailTrace_543209 : CollatzResearch.WordTrace tailWord_543209 prefixEnd_543209 247935389198462600879407 := by
  unfold tailWord_543209
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812459889054040556296681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13208306592702693704197787 19812459889054040556296681)
  ·
    refine ⟨14859344916790530417222511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19812459889054040556296681 14859344916790530417222511)
    ·
      refine ⟨22289017375185795625833767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859344916790530417222511 22289017375185795625833767)
      ·
        refine ⟨33433526062778693438750651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22289017375185795625833767 33433526062778693438750651)
        ·
          refine ⟨50150289094168040158125977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33433526062778693438750651 50150289094168040158125977)
          ·
            refine ⟨37612716820626030118594483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50150289094168040158125977 37612716820626030118594483)
            ·
              refine ⟨56419075230939045177891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37612716820626030118594483 56419075230939045177891725)
              ·
                refine ⟨21157153211602141941709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56419075230939045177891725 21157153211602141941709397)
                ·
                  refine ⟨247935389198462600879407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21157153211602141941709397 247935389198462600879407)
                  ·
                    rfl

theorem cell20_543209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_543209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543209 prefixEnd_543209 := by exact prefixLift 543209
  have htrace : WordTrace (prefixWord ++ tailWord_543209) baseStart_543209 baseEnd_543209 := by
    simpa [prefixWord, tailWord_543209, baseEnd_543209] using wordTrace_append hprefix tailTrace_543209
  have hstable : (prefixWord ++ tailWord_543209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543209).length < 2 ^ (prefixWord ++ tailWord_543209).sum := by decide
  have hdescent : baseEnd_543209 < baseStart_543209 := by decide
  rcases family_descends (prefixWord ++ tailWord_543209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543218 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_543218 : Nat := 118140960795 + 543218 * 2 ^ 59
def prefixEnd_543218 : Nat := 4983230072969 + 3 ^ 40 * 543218 * 2
def baseEnd_543218 : Nat := 247939497043698569579371

theorem tailTrace_543218 : CollatzResearch.WordTrace tailWord_543218 prefixEnd_543218 247939497043698569579371 := by
  unfold tailWord_543218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953197036505358773343577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13208525430680956728916205 4953197036505358773343577)
  ·
    refine ⟨3714897777379019080007683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4953197036505358773343577 3714897777379019080007683)
    ·
      refine ⟨5572346666068528620011525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714897777379019080007683 5572346666068528620011525)
      ·
        refine ⟨1044814999887849116252161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5572346666068528620011525 1044814999887849116252161)
        ·
          refine ⟨783611249915886837189121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044814999887849116252161 783611249915886837189121)
          ·
            refine ⟨587708437436915127891841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 783611249915886837189121 587708437436915127891841)
            ·
              refine ⟨440781328077686345918881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587708437436915127891841 440781328077686345918881)
              ·
                refine ⟨330585996058264759439161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440781328077686345918881 330585996058264759439161)
                ·
                  refine ⟨247939497043698569579371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330585996058264759439161 247939497043698569579371)
                  ·
                    rfl

theorem cell20_543218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_543218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543218 prefixEnd_543218 := by exact prefixLift 543218
  have htrace : WordTrace (prefixWord ++ tailWord_543218) baseStart_543218 baseEnd_543218 := by
    simpa [prefixWord, tailWord_543218, baseEnd_543218] using wordTrace_append hprefix tailTrace_543218
  have hstable : (prefixWord ++ tailWord_543218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543218).length < 2 ^ (prefixWord ++ tailWord_543218).sum := by decide
  have hdescent : baseEnd_543218 < baseStart_543218 := by decide
  rcases family_descends (prefixWord ++ tailWord_543218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543219 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_543219 : Nat := 118140960795 + 543219 * 2 ^ 59
def prefixEnd_543219 : Nat := 4983230072969 + 3 ^ 40 * 543219 * 2
def baseEnd_543219 : Nat := 247939953470947010546033

theorem tailTrace_543219 : CollatzResearch.WordTrace tailWord_543219 prefixEnd_543219 247939953470947010546033 := by
  unfold tailWord_543219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812824619017812264160711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13208549746011874842773807 19812824619017812264160711)
  ·
    refine ⟨29719236928526718396241067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19812824619017812264160711 29719236928526718396241067)
    ·
      refine ⟨44578855392790077594361601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29719236928526718396241067 44578855392790077594361601)
      ·
        refine ⟨33434141544592558195771201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44578855392790077594361601 33434141544592558195771201)
        ·
          refine ⟨25075606158444418646828401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33434141544592558195771201 25075606158444418646828401)
          ·
            refine ⟨18806704618833313985121301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25075606158444418646828401 18806704618833313985121301)
            ·
              refine ⟨881564279007811593052561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18806704618833313985121301 881564279007811593052561)
              ·
                refine ⟨661173209255858694789421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881564279007811593052561 661173209255858694789421)
                ·
                  refine ⟨247939953470947010546033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661173209255858694789421 247939953470947010546033)
                  ·
                    rfl

theorem cell20_543219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_543219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543219 prefixEnd_543219 := by exact prefixLift 543219
  have htrace : WordTrace (prefixWord ++ tailWord_543219) baseStart_543219 baseEnd_543219 := by
    simpa [prefixWord, tailWord_543219, baseEnd_543219] using wordTrace_append hprefix tailTrace_543219
  have hstable : (prefixWord ++ tailWord_543219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543219).length < 2 ^ (prefixWord ++ tailWord_543219).sum := by decide
  have hdescent : baseEnd_543219 < baseStart_543219 := by decide
  rcases family_descends (prefixWord ++ tailWord_543219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543222 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_543222 : Nat := 118140960795 + 543222 * 2 ^ 59
def prefixEnd_543222 : Nat := 4983230072969 + 3 ^ 40 * 543222 * 2
def baseEnd_543222 : Nat := 247941322752692333446021

theorem tailTrace_543222 : CollatzResearch.WordTrace tailWord_543222 prefixEnd_543222 247941322752692333446021 := by
  unfold tailWord_543222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238308377375433986032495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13208622692004629184346613 1238308377375433986032495)
  ·
    refine ⟨1857462566063150979048743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238308377375433986032495 1857462566063150979048743)
    ·
      refine ⟨2786193849094726468573115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1857462566063150979048743 2786193849094726468573115)
      ·
        refine ⟨4179290773642089702859673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786193849094726468573115 4179290773642089702859673)
        ·
          refine ⟨3134468080231567277144755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179290773642089702859673 3134468080231567277144755)
          ·
            refine ⟨4701702120347350915717133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134468080231567277144755 4701702120347350915717133)
            ·
              refine ⟨1763138295130256593393925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4701702120347350915717133 1763138295130256593393925)
              ·
                refine ⟨330588430336923111261361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1763138295130256593393925 330588430336923111261361)
                ·
                  refine ⟨247941322752692333446021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330588430336923111261361 247941322752692333446021)
                  ·
                    rfl

theorem cell20_543222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_543222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543222 prefixEnd_543222 := by exact prefixLift 543222
  have htrace : WordTrace (prefixWord ++ tailWord_543222) baseStart_543222 baseEnd_543222 := by
    simpa [prefixWord, tailWord_543222, baseEnd_543222] using wordTrace_append hprefix tailTrace_543222
  have hstable : (prefixWord ++ tailWord_543222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543222).length < 2 ^ (prefixWord ++ tailWord_543222).sum := by decide
  have hdescent : baseEnd_543222 < baseStart_543222 := by decide
  rcases family_descends (prefixWord ++ tailWord_543222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543236 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_543236 : Nat := 118140960795 + 543236 * 2 ^ 59
def prefixEnd_543236 : Nat := 4983230072969 + 3 ^ 40 * 543236 * 2
def baseEnd_543236 : Nat := 247947712734170506979297

theorem tailTrace_543236 : CollatzResearch.WordTrace tailWord_543236 prefixEnd_543236 247947712734170506979297 := by
  unfold tailWord_543236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906722329978112083764781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13208963106637482778353041 9906722329978112083764781)
  ·
    refine ⟨3715020873741792031411793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9906722329978112083764781 3715020873741792031411793)
    ·
      refine ⟨2786265655306344023558845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715020873741792031411793 2786265655306344023558845)
      ·
        refine ⟨1044849620739879008834567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2786265655306344023558845 1044849620739879008834567)
        ·
          refine ⟨1567274431109818513251851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044849620739879008834567 1567274431109818513251851)
          ·
            refine ⟨2350911646664727769877777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567274431109818513251851 2350911646664727769877777)
            ·
              refine ⟨1763183734998545827408333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350911646664727769877777 1763183734998545827408333)
              ·
                refine ⟨661193900624454685278125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763183734998545827408333 661193900624454685278125)
                ·
                  refine ⟨247947712734170506979297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661193900624454685278125 247947712734170506979297)
                  ·
                    rfl

theorem cell20_543236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_543236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543236 prefixEnd_543236 := by exact prefixLift 543236
  have htrace : WordTrace (prefixWord ++ tailWord_543236) baseStart_543236 baseEnd_543236 := by
    simpa [prefixWord, tailWord_543236, baseEnd_543236] using wordTrace_append hprefix tailTrace_543236
  have hstable : (prefixWord ++ tailWord_543236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543236).length < 2 ^ (prefixWord ++ tailWord_543236).sum := by decide
  have hdescent : baseEnd_543236 < baseStart_543236 := by decide
  rcases family_descends (prefixWord ++ tailWord_543236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543240 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_543240 : Nat := 118140960795 + 543240 * 2 ^ 59
def prefixEnd_543240 : Nat := 4983230072969 + 3 ^ 40 * 543240 * 2
def baseEnd_543240 : Nat := 247949538443164270845947

theorem tailTrace_543240 : CollatzResearch.WordTrace tailWord_543240 prefixEnd_543240 247949538443164270845947 := by
  unfold tailWord_543240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906795275970866425337587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13209060367961155233783449 9906795275970866425337587)
  ·
    refine ⟨14860192913956299638006381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9906795275970866425337587 14860192913956299638006381)
    ·
      refine ⟨5572572342733612364252393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14860192913956299638006381 5572572342733612364252393)
      ·
        refine ⟨4179429257050209273189295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5572572342733612364252393 4179429257050209273189295)
        ·
          refine ⟨6269143885575313909783943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179429257050209273189295 6269143885575313909783943)
          ·
            refine ⟨9403715828362970864675915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269143885575313909783943 9403715828362970864675915)
            ·
              refine ⟨14105573742544456297013873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9403715828362970864675915 14105573742544456297013873)
              ·
                refine ⟨10579180306908342222760405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14105573742544456297013873 10579180306908342222760405)
                ·
                  refine ⟨247949538443164270845947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10579180306908342222760405 247949538443164270845947)
                  ·
                    rfl

theorem cell20_543240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_543240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543240 prefixEnd_543240 := by exact prefixLift 543240
  have htrace : WordTrace (prefixWord ++ tailWord_543240) baseStart_543240 baseEnd_543240 := by
    simpa [prefixWord, tailWord_543240, baseEnd_543240] using wordTrace_append hprefix tailTrace_543240
  have hstable : (prefixWord ++ tailWord_543240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543240).length < 2 ^ (prefixWord ++ tailWord_543240).sum := by decide
  have hdescent : baseEnd_543240 < baseStart_543240 := by decide
  rcases family_descends (prefixWord ++ tailWord_543240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543247 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_543247 : Nat := 118140960795 + 543247 * 2 ^ 59
def prefixEnd_543247 : Nat := 4983230072969 + 3 ^ 40 * 543247 * 2
def baseEnd_543247 : Nat := 247952733433903357612585

theorem tailTrace_543247 : CollatzResearch.WordTrace tailWord_543247 prefixEnd_543247 247952733433903357612585 := by
  unfold tailWord_543247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19813845862916373046179995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13209230575277582030786663 19813845862916373046179995)
  ·
    refine ⟨29720768794374559569269993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19813845862916373046179995 29720768794374559569269993)
    ·
      refine ⟨22290576595780919676952495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29720768794374559569269993 22290576595780919676952495)
      ·
        refine ⟨33435864893671379515428743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22290576595780919676952495 33435864893671379515428743)
        ·
          refine ⟨50153797340507069273143115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33435864893671379515428743 50153797340507069273143115)
          ·
            refine ⟨75230696010760603909714673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50153797340507069273143115 75230696010760603909714673)
            ·
              refine ⟨56423022008070452932286005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75230696010760603909714673 56423022008070452932286005)
              ·
                refine ⟨5289658313256604962401813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56423022008070452932286005 5289658313256604962401813)
                ·
                  refine ⟨247952733433903357612585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5289658313256604962401813 247952733433903357612585)
                  ·
                    rfl

theorem cell20_543247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_543247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543247 prefixEnd_543247 := by exact prefixLift 543247
  have htrace : WordTrace (prefixWord ++ tailWord_543247) baseStart_543247 baseEnd_543247 := by
    simpa [prefixWord, tailWord_543247, baseEnd_543247] using wordTrace_append hprefix tailTrace_543247
  have hstable : (prefixWord ++ tailWord_543247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543247).length < 2 ^ (prefixWord ++ tailWord_543247).sum := by decide
  have hdescent : baseEnd_543247 < baseStart_543247 := by decide
  rcases family_descends (prefixWord ++ tailWord_543247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543260 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_543260 : Nat := 118140960795 + 543260 * 2 ^ 59
def prefixEnd_543260 : Nat := 4983230072969 + 3 ^ 40 * 543260 * 2
def baseEnd_543260 : Nat := 247958666988133090179199

theorem tailTrace_543260 : CollatzResearch.WordTrace tailWord_543260 prefixEnd_543260 247958666988133090179199 := by
  unfold tailWord_543260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907160005934638133201617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13209546674579517510935489 9907160005934638133201617)
  ·
    refine ⟨7430370004450978599901213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9907160005934638133201617 7430370004450978599901213)
    ·
      refine ⟨2786388751669116974962955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7430370004450978599901213 2786388751669116974962955)
      ·
        refine ⟨4179583127503675462444433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786388751669116974962955 4179583127503675462444433)
        ·
          refine ⟨3134687345627756596833325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179583127503675462444433 3134687345627756596833325)
          ·
            refine ⟨1175507754610408723812497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3134687345627756596833325 1175507754610408723812497)
            ·
              refine ⟨881630815957806542859373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175507754610408723812497 881630815957806542859373)
              ·
                refine ⟨330611555984177453572265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881630815957806542859373 330611555984177453572265)
                ·
                  refine ⟨247958666988133090179199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330611555984177453572265 247958666988133090179199)
                  ·
                    rfl

theorem cell20_543260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_543260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543260 prefixEnd_543260 := by exact prefixLift 543260
  have htrace : WordTrace (prefixWord ++ tailWord_543260) baseStart_543260 baseEnd_543260 := by
    simpa [prefixWord, tailWord_543260, baseEnd_543260] using wordTrace_append hprefix tailTrace_543260
  have hstable : (prefixWord ++ tailWord_543260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543260).length < 2 ^ (prefixWord ++ tailWord_543260).sum := by decide
  have hdescent : baseEnd_543260 < baseStart_543260 := by decide
  rcases family_descends (prefixWord ++ tailWord_543260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543274 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_543274 : Nat := 118140960795 + 543274 * 2 ^ 59
def prefixEnd_543274 : Nat := 4983230072969 + 3 ^ 40 * 543274 * 2
def baseEnd_543274 : Nat := 247965056969611263712475

theorem tailTrace_543274 : CollatzResearch.WordTrace tailWord_543274 prefixEnd_543274 247965056969611263712475 := by
  unfold tailWord_543274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953707658454639164353219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13209887089212371104941917 4953707658454639164353219)
  ·
    refine ⟨7430561487681958746529829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953707658454639164353219 7430561487681958746529829)
    ·
      refine ⟨1393230278940367264974343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7430561487681958746529829 1393230278940367264974343)
      ·
        refine ⟨2089845418410550897461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393230278940367264974343 2089845418410550897461515)
        ·
          refine ⟨3134768127615826346192273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089845418410550897461515 3134768127615826346192273)
          ·
            refine ⟨2351076095711869759644205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134768127615826346192273 2351076095711869759644205)
            ·
              refine ⟨881653535891951159866577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351076095711869759644205 881653535891951159866577)
              ·
                refine ⟨661240151918963369899933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881653535891951159866577 661240151918963369899933)
                ·
                  refine ⟨247965056969611263712475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661240151918963369899933 247965056969611263712475)
                  ·
                    rfl

theorem cell20_543274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_543274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543274 prefixEnd_543274 := by exact prefixLift 543274
  have htrace : WordTrace (prefixWord ++ tailWord_543274) baseStart_543274 baseEnd_543274 := by
    simpa [prefixWord, tailWord_543274, baseEnd_543274] using wordTrace_append hprefix tailTrace_543274
  have hstable : (prefixWord ++ tailWord_543274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543274).length < 2 ^ (prefixWord ++ tailWord_543274).sum := by decide
  have hdescent : baseEnd_543274 < baseStart_543274 := by decide
  rcases family_descends (prefixWord ++ tailWord_543274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543281 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 2]
def baseStart_543281 : Nat := 118140960795 + 543281 * 2 ^ 59
def prefixEnd_543281 : Nat := 4983230072969 + 3 ^ 40 * 543281 * 2
def baseEnd_543281 : Nat := 247968251960350350479113

theorem tailTrace_543281 : CollatzResearch.WordTrace tailWord_543281 prefixEnd_543281 247968251960350350479113 := by
  unfold tailWord_543281
  simp only [CollatzResearch.WordTrace]
  refine ⟨19815085944793196852917697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13210057296528797901945131 19815085944793196852917697)
  ·
    refine ⟨14861314458594897639688273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19815085944793196852917697 14861314458594897639688273)
    ·
      refine ⟨11145985843946173229766205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14861314458594897639688273 11145985843946173229766205)
      ·
        refine ⟨4179744691479814961162327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11145985843946173229766205 4179744691479814961162327)
        ·
          refine ⟨6269617037219722441743491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179744691479814961162327 6269617037219722441743491)
          ·
            refine ⟨9404425555829583662615237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269617037219722441743491 9404425555829583662615237)
            ·
              refine ⟨1763329791718046936740357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9404425555829583662615237 1763329791718046936740357)
              ·
                refine ⟨330624335947133800638817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1763329791718046936740357 330624335947133800638817)
                ·
                  refine ⟨247968251960350350479113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330624335947133800638817 247968251960350350479113)
                  ·
                    rfl

theorem cell20_543281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_543281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543281 prefixEnd_543281 := by exact prefixLift 543281
  have htrace : WordTrace (prefixWord ++ tailWord_543281) baseStart_543281 baseEnd_543281 := by
    simpa [prefixWord, tailWord_543281, baseEnd_543281] using wordTrace_append hprefix tailTrace_543281
  have hstable : (prefixWord ++ tailWord_543281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543281).length < 2 ^ (prefixWord ++ tailWord_543281).sum := by decide
  have hdescent : baseEnd_543281 < baseStart_543281 := by decide
  rcases family_descends (prefixWord ++ tailWord_543281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543336 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_543336 : Nat := 118140960795 + 543336 * 2 ^ 59
def prefixEnd_543336 : Nat := 4983230072969 + 3 ^ 40 * 543336 * 2
def baseEnd_543336 : Nat := 247993355459014603645555

theorem tailTrace_543336 : CollatzResearch.WordTrace tailWord_543336 prefixEnd_543336 247993355459014603645555 := by
  unfold tailWord_543336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908545979796970623084931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13211394639729294164113241 9908545979796970623084931)
  ·
    refine ⟨14862818969695455934627397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9908545979796970623084931 14862818969695455934627397)
    ·
      refine ⟨2786778556817897987742637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14862818969695455934627397 2786778556817897987742637)
      ·
        refine ⟨1045041958806711745403489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2786778556817897987742637 1045041958806711745403489)
        ·
          refine ⟨783781469105033809052617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045041958806711745403489 783781469105033809052617)
          ·
            refine ⟨587836101828775356789463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 783781469105033809052617 587836101828775356789463)
            ·
              refine ⟨881754152743163035184195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587836101828775356789463 881754152743163035184195)
              ·
                refine ⟨1322631229114744552776293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881754152743163035184195 1322631229114744552776293)
                ·
                  refine ⟨247993355459014603645555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322631229114744552776293 247993355459014603645555)
                  ·
                    rfl

theorem cell20_543336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_543336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543336 prefixEnd_543336 := by exact prefixLift 543336
  have htrace : WordTrace (prefixWord ++ tailWord_543336) baseStart_543336 baseEnd_543336 := by
    simpa [prefixWord, tailWord_543336, baseEnd_543336] using wordTrace_append hprefix tailTrace_543336
  have hstable : (prefixWord ++ tailWord_543336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543336).length < 2 ^ (prefixWord ++ tailWord_543336).sum := by decide
  have hdescent : baseEnd_543336 < baseStart_543336 := by decide
  rcases family_descends (prefixWord ++ tailWord_543336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543340 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_543340 : Nat := 118140960795 + 543340 * 2 ^ 59
def prefixEnd_543340 : Nat := 4983230072969 + 3 ^ 40 * 543340 * 2
def baseEnd_543340 : Nat := 247995181168008367512205

theorem tailTrace_543340 : CollatzResearch.WordTrace tailWord_543340 prefixEnd_543340 247995181168008367512205 := by
  unfold tailWord_543340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908618925789724964657737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13211491901052966619543649 9908618925789724964657737)
  ·
    refine ⟨7431464194342293723493303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9908618925789724964657737 7431464194342293723493303)
    ·
      refine ⟨11147196291513440585239955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431464194342293723493303 11147196291513440585239955)
      ·
        refine ⟨16720794437270160877859933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11147196291513440585239955 16720794437270160877859933)
        ·
          refine ⟨6270297913976310329197475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16720794437270160877859933 6270297913976310329197475)
          ·
            refine ⟨9405446870964465493796213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270297913976310329197475 9405446870964465493796213)
            ·
              refine ⟨881760644152918640043395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9405446870964465493796213 881760644152918640043395)
              ·
                refine ⟨1322640966229377960065093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881760644152918640043395 1322640966229377960065093)
                ·
                  refine ⟨247995181168008367512205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322640966229377960065093 247995181168008367512205)
                  ·
                    rfl

theorem cell20_543340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_543340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543340 prefixEnd_543340 := by exact prefixLift 543340
  have htrace : WordTrace (prefixWord ++ tailWord_543340) baseStart_543340 baseEnd_543340 := by
    simpa [prefixWord, tailWord_543340, baseEnd_543340] using wordTrace_append hprefix tailTrace_543340
  have hstable : (prefixWord ++ tailWord_543340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543340).length < 2 ^ (prefixWord ++ tailWord_543340).sum := by decide
  have hdescent : baseEnd_543340 < baseStart_543340 := by decide
  rcases family_descends (prefixWord ++ tailWord_543340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543346 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_543346 : Nat := 118140960795 + 543346 * 2 ^ 59
def prefixEnd_543346 : Nat := 4983230072969 + 3 ^ 40 * 543346 * 2
def baseEnd_543346 : Nat := 247997919731499013312181

theorem tailTrace_543346 : CollatzResearch.WordTrace tailWord_543346 prefixEnd_543346 247997919731499013312181 := by
  unfold tailWord_543346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954364172389428238508473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13211637793038475302689261 4954364172389428238508473)
  ·
    refine ⟨3715773129292071178881355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4954364172389428238508473 3715773129292071178881355)
    ·
      refine ⟨5573659693938106768322033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715773129292071178881355 5573659693938106768322033)
      ·
        refine ⟨4180244770453580076241525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5573659693938106768322033 4180244770453580076241525)
        ·
          refine ⟨391897947230023132147643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4180244770453580076241525 391897947230023132147643)
          ·
            refine ⟨587846920845034698221465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391897947230023132147643 587846920845034698221465)
            ·
              refine ⟨440885190633776023666099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587846920845034698221465 440885190633776023666099)
              ·
                refine ⟨661327785950664035499149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440885190633776023666099 661327785950664035499149)
                ·
                  refine ⟨247997919731499013312181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661327785950664035499149 247997919731499013312181)
                  ·
                    rfl

theorem cell20_543346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_543346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543346 prefixEnd_543346 := by exact prefixLift 543346
  have htrace : WordTrace (prefixWord ++ tailWord_543346) baseStart_543346 baseEnd_543346 := by
    simpa [prefixWord, tailWord_543346, baseEnd_543346] using wordTrace_append hprefix tailTrace_543346
  have hstable : (prefixWord ++ tailWord_543346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543346).length < 2 ^ (prefixWord ++ tailWord_543346).sum := by decide
  have hdescent : baseEnd_543346 < baseStart_543346 := by decide
  rcases family_descends (prefixWord ++ tailWord_543346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543388 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_543388 : Nat := 118140960795 + 543388 * 2 ^ 59
def prefixEnd_543388 : Nat := 4983230072969 + 3 ^ 40 * 543388 * 2
def baseEnd_543388 : Nat := 248017089675933533912009

theorem tailTrace_543388 : CollatzResearch.WordTrace tailWord_543388 prefixEnd_543388 248017089675933533912009 := by
  unfold tailWord_543388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909494277702777063531409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13212659036937036084708545 9909494277702777063531409)
  ·
    refine ⟨7432120708277082797648557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9909494277702777063531409 7432120708277082797648557)
    ·
      refine ⟨2787045265603906049118209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7432120708277082797648557 2787045265603906049118209)
      ·
        refine ⟨2090283949202929536838657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2787045265603906049118209 2090283949202929536838657)
        ·
          refine ⟨1567712961902197152628993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2090283949202929536838657 1567712961902197152628993)
          ·
            refine ⟨1175784721426647864471745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1567712961902197152628993 1175784721426647864471745)
            ·
              refine ⟨881838541069985898353809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175784721426647864471745 881838541069985898353809)
              ·
                refine ⟨661378905802489423765357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881838541069985898353809 661378905802489423765357)
                ·
                  refine ⟨248017089675933533912009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661378905802489423765357 248017089675933533912009)
                  ·
                    rfl

theorem cell20_543388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_543388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543388 prefixEnd_543388 := by exact prefixLift 543388
  have htrace : WordTrace (prefixWord ++ tailWord_543388) baseStart_543388 baseEnd_543388 := by
    simpa [prefixWord, tailWord_543388, baseEnd_543388] using wordTrace_append hprefix tailTrace_543388
  have hstable : (prefixWord ++ tailWord_543388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543388).length < 2 ^ (prefixWord ++ tailWord_543388).sum := by decide
  have hdescent : baseEnd_543388 < baseStart_543388 := by decide
  rcases family_descends (prefixWord ++ tailWord_543388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543447 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_543447 : Nat := 118140960795 + 543447 * 2 ^ 59
def prefixEnd_543447 : Nat := 4983230072969 + 3 ^ 40 * 543447 * 2
def baseEnd_543447 : Nat := 248044018883591550945101

theorem tailTrace_543447 : CollatzResearch.WordTrace tailWord_543447 prefixEnd_543447 248044018883591550945101 := by
  unfold tailWord_543447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19821140462191807203460595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13214093641461204802307063 19821140462191807203460595)
  ·
    refine ⟨29731710693287710805190893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19821140462191807203460595 29731710693287710805190893)
    ·
      refine ⟨11149391509982891551946585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29731710693287710805190893 11149391509982891551946585)
      ·
        refine ⟨8362043632487168663959939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11149391509982891551946585 8362043632487168663959939)
        ·
          refine ⟨12543065448730752995939909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8362043632487168663959939 12543065448730752995939909)
          ·
            refine ⟨2351824771637016186738733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12543065448730752995939909 2351824771637016186738733)
            ·
              refine ⟨881934289363881070027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351824771637016186738733 881934289363881070027025)
              ·
                refine ⟨661450717022910802520269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881934289363881070027025 661450717022910802520269)
                ·
                  refine ⟨248044018883591550945101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661450717022910802520269 248044018883591550945101)
                  ·
                    rfl

theorem cell20_543447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_543447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543447 prefixEnd_543447 := by exact prefixLift 543447
  have htrace : WordTrace (prefixWord ++ tailWord_543447) baseStart_543447 baseEnd_543447 := by
    simpa [prefixWord, tailWord_543447, baseEnd_543447] using wordTrace_append hprefix tailTrace_543447
  have hstable : (prefixWord ++ tailWord_543447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543447).length < 2 ^ (prefixWord ++ tailWord_543447).sum := by decide
  have hdescent : baseEnd_543447 < baseStart_543447 := by decide
  rcases family_descends (prefixWord ++ tailWord_543447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543513 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_543513 : Nat := 118140960795 + 543513 * 2 ^ 59
def prefixEnd_543513 : Nat := 4983230072969 + 3 ^ 40 * 543513 * 2
def baseEnd_543513 : Nat := 248074143081988654744831

theorem tailTrace_543513 : CollatzResearch.WordTrace tailWord_543513 prefixEnd_543513 248074143081988654744831 := by
  unfold tailWord_543513
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823547679952700475363193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13215698453301800316908795 19823547679952700475363193)
  ·
    refine ⟨14867660759964525356522395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19823547679952700475363193 14867660759964525356522395)
    ·
      refine ⟨22301491139946788034783593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14867660759964525356522395 22301491139946788034783593)
      ·
        refine ⟨16726118354960091026087695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22301491139946788034783593 16726118354960091026087695)
        ·
          refine ⟨25089177532440136539131543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16726118354960091026087695 25089177532440136539131543)
          ·
            refine ⟨37633766298660204808697315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25089177532440136539131543 37633766298660204808697315)
            ·
              refine ⟨56450649447990307213045973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37633766298660204808697315 56450649447990307213045973)
              ·
                refine ⟨1323062096437272825305765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56450649447990307213045973 1323062096437272825305765)
                ·
                  refine ⟨248074143081988654744831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323062096437272825305765 248074143081988654744831)
                  ·
                    rfl

theorem cell20_543513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_543513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543513 prefixEnd_543513 := by exact prefixLift 543513
  have htrace : WordTrace (prefixWord ++ tailWord_543513) baseStart_543513 baseEnd_543513 := by
    simpa [prefixWord, tailWord_543513, baseEnd_543513] using wordTrace_append hprefix tailTrace_543513
  have hstable : (prefixWord ++ tailWord_543513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543513).length < 2 ^ (prefixWord ++ tailWord_543513).sum := by decide
  have hdescent : baseEnd_543513 < baseStart_543513 := by decide
  rcases family_descends (prefixWord ++ tailWord_543513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543561 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_543561 : Nat := 118140960795 + 543561 * 2 ^ 59
def prefixEnd_543561 : Nat := 4983230072969 + 3 ^ 40 * 543561 * 2
def baseEnd_543561 : Nat := 248096051589913821144635

theorem tailTrace_543561 : CollatzResearch.WordTrace tailWord_543561 prefixEnd_543561 248096051589913821144635 := by
  unfold tailWord_543561
  simp only [CollatzResearch.WordTrace]
  refine ⟨19825298383778804673110537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13216865589185869782073691 19825298383778804673110537)
  ·
    refine ⟨14868973787834103504832903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19825298383778804673110537 14868973787834103504832903)
    ·
      refine ⟨22303460681751155257249355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868973787834103504832903 22303460681751155257249355)
      ·
        refine ⟨33455191022626732885874033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22303460681751155257249355 33455191022626732885874033)
        ·
          refine ⟨25091393266970049664405525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33455191022626732885874033 25091393266970049664405525)
          ·
            refine ⟨1176159059389221078019009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25091393266970049664405525 1176159059389221078019009)
            ·
              refine ⟨882119294541915808514257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176159059389221078019009 882119294541915808514257)
              ·
                refine ⟨661589470906436856385693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882119294541915808514257 661589470906436856385693)
                ·
                  refine ⟨248096051589913821144635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661589470906436856385693 248096051589913821144635)
                  ·
                    rfl

theorem cell20_543561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_543561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543561 prefixEnd_543561 := by exact prefixLift 543561
  have htrace : WordTrace (prefixWord ++ tailWord_543561) baseStart_543561 baseEnd_543561 := by
    simpa [prefixWord, tailWord_543561, baseEnd_543561] using wordTrace_append hprefix tailTrace_543561
  have hstable : (prefixWord ++ tailWord_543561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543561).length < 2 ^ (prefixWord ++ tailWord_543561).sum := by decide
  have hdescent : baseEnd_543561 < baseStart_543561 := by decide
  rcases family_descends (prefixWord ++ tailWord_543561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543564 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_543564 : Nat := 118140960795 + 543564 * 2 ^ 59
def prefixEnd_543564 : Nat := 4983230072969 + 3 ^ 40 * 543564 * 2
def baseEnd_543564 : Nat := 248097420871659144044623

theorem tailTrace_543564 : CollatzResearch.WordTrace tailWord_543564 prefixEnd_543564 248097420871659144044623 := by
  unfold tailWord_543564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912703901383968092734873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13216938535178624123646497 9912703901383968092734873)
  ·
    refine ⟨7434527926037976069551155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9912703901383968092734873 7434527926037976069551155)
    ·
      refine ⟨11151791889056964104326733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7434527926037976069551155 11151791889056964104326733)
      ·
        refine ⟨4181921958396361539122525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11151791889056964104326733 4181921958396361539122525)
        ·
          refine ⟨1568220734398635577170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4181921958396361539122525 1568220734398635577170947)
          ·
            refine ⟨2352331101597953365756421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568220734398635577170947 2352331101597953365756421)
            ·
              refine ⟨441062081549616256079329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2352331101597953365756421 441062081549616256079329)
              ·
                refine ⟨330796561162212192059497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441062081549616256079329 330796561162212192059497)
                ·
                  refine ⟨248097420871659144044623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330796561162212192059497 248097420871659144044623)
                  ·
                    rfl

theorem cell20_543564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_543564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543564 prefixEnd_543564 := by exact prefixLift 543564
  have htrace : WordTrace (prefixWord ++ tailWord_543564) baseStart_543564 baseEnd_543564 := by
    simpa [prefixWord, tailWord_543564, baseEnd_543564] using wordTrace_append hprefix tailTrace_543564
  have hstable : (prefixWord ++ tailWord_543564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543564).length < 2 ^ (prefixWord ++ tailWord_543564).sum := by decide
  have hdescent : baseEnd_543564 < baseStart_543564 := by decide
  rcases family_descends (prefixWord ++ tailWord_543564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543575 : List Nat := [1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_543575 : Nat := 118140960795 + 543575 * 2 ^ 59
def prefixEnd_543575 : Nat := 4983230072969 + 3 ^ 40 * 543575 * 2
def baseEnd_543575 : Nat := 82700813857130664892637

theorem tailTrace_543575 : CollatzResearch.WordTrace tailWord_543575 prefixEnd_543575 82700813857130664892637 := by
  unfold tailWord_543575
  simp only [CollatzResearch.WordTrace]
  refine ⟨19825809005728085064120179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13217206003818723376080119 19825809005728085064120179)
  ·
    refine ⟨29738713508592127596180269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19825809005728085064120179 29738713508592127596180269)
    ·
      refine ⟨11152017565722047848567601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29738713508592127596180269 11152017565722047848567601)
      ·
        refine ⟨8364013174291535886425701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11152017565722047848567601 8364013174291535886425701)
        ·
          refine ⟨1568252470179662978704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8364013174291535886425701 1568252470179662978704819)
          ·
            refine ⟨2352378705269494468057229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568252470179662978704819 2352378705269494468057229)
            ·
              refine ⟨882142014476060425521461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2352378705269494468057229 882142014476060425521461)
              ·
                refine ⟨82700813857130664892637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 882142014476060425521461 82700813857130664892637)
                ·
                  rfl

theorem cell20_543575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_543575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543575 prefixEnd_543575 := by exact prefixLift 543575
  have htrace : WordTrace (prefixWord ++ tailWord_543575) baseStart_543575 baseEnd_543575 := by
    simpa [prefixWord, tailWord_543575, baseEnd_543575] using wordTrace_append hprefix tailTrace_543575
  have hstable : (prefixWord ++ tailWord_543575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543575).length < 2 ^ (prefixWord ++ tailWord_543575).sum := by decide
  have hdescent : baseEnd_543575 < baseStart_543575 := by decide
  rcases family_descends (prefixWord ++ tailWord_543575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543589 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_543589 : Nat := 118140960795 + 543589 * 2 ^ 59
def prefixEnd_543589 : Nat := 4983230072969 + 3 ^ 40 * 543589 * 2
def baseEnd_543589 : Nat := 248108831552870168211187

theorem tailTrace_543589 : CollatzResearch.WordTrace tailWord_543589 prefixEnd_543589 248108831552870168211187 := by
  unfold tailWord_543589
  simp only [CollatzResearch.WordTrace]
  refine ⟨19826319627677365455129821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13217546418451576970086547 19826319627677365455129821)
  ·
    refine ⟨7434869860379012045673683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19826319627677365455129821 7434869860379012045673683)
    ·
      refine ⟨11152304790568518068510525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7434869860379012045673683 11152304790568518068510525)
      ·
        refine ⟨4182114296463194275691447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11152304790568518068510525 4182114296463194275691447)
        ·
          refine ⟨6273171444694791413537171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182114296463194275691447 6273171444694791413537171)
          ·
            refine ⟨9409757167042187120305757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273171444694791413537171 9409757167042187120305757)
            ·
              refine ⟨3528658937640820170114659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9409757167042187120305757 3528658937640820170114659)
              ·
                refine ⟨5292988406461230255171989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528658937640820170114659 5292988406461230255171989)
                ·
                  refine ⟨248108831552870168211187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5292988406461230255171989 248108831552870168211187)
                  ·
                    rfl

theorem cell20_543589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_543589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543589 prefixEnd_543589 := by exact prefixLift 543589
  have htrace : WordTrace (prefixWord ++ tailWord_543589) baseStart_543589 baseEnd_543589 := by
    simpa [prefixWord, tailWord_543589, baseEnd_543589] using wordTrace_append hprefix tailTrace_543589
  have hstable : (prefixWord ++ tailWord_543589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543589).length < 2 ^ (prefixWord ++ tailWord_543589).sum := by decide
  have hdescent : baseEnd_543589 < baseStart_543589 := by decide
  rcases family_descends (prefixWord ++ tailWord_543589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543592 : List Nat := [2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_543592 : Nat := 118140960795 + 543592 * 2 ^ 59
def prefixEnd_543592 : Nat := 4983230072969 + 3 ^ 40 * 543592 * 2
def baseEnd_543592 : Nat := 82703400278205163703725

theorem tailTrace_543592 : CollatzResearch.WordTrace tailWord_543592 prefixEnd_543592 82703400278205163703725 := by
  unfold tailWord_543592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9913214523333248483744515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13217619364444331311659353 9913214523333248483744515)
  ·
    refine ⟨14869821784999872725616773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9913214523333248483744515 14869821784999872725616773)
    ·
      refine ⟨2788091584687476136053145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14869821784999872725616773 2788091584687476136053145)
      ·
        refine ⟨2091068688515607102039859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2788091584687476136053145 2091068688515607102039859)
        ·
          refine ⟨3136603032773410653059789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091068688515607102039859 3136603032773410653059789)
          ·
            refine ⟨1176226137290028994897421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3136603032773410653059789 1176226137290028994897421)
            ·
              refine ⟨441084801483760873086533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1176226137290028994897421 441084801483760873086533)
              ·
                refine ⟨82703400278205163703725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441084801483760873086533 82703400278205163703725)
                ·
                  rfl

theorem cell20_543592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_543592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543592 prefixEnd_543592 := by exact prefixLift 543592
  have htrace : WordTrace (prefixWord ++ tailWord_543592) baseStart_543592 baseEnd_543592 := by
    simpa [prefixWord, tailWord_543592, baseEnd_543592] using wordTrace_append hprefix tailTrace_543592
  have hstable : (prefixWord ++ tailWord_543592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543592).length < 2 ^ (prefixWord ++ tailWord_543592).sum := by decide
  have hdescent : baseEnd_543592 < baseStart_543592 := by decide
  rcases family_descends (prefixWord ++ tailWord_543592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543623 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 2]
def baseStart_543623 : Nat := 118140960795 + 543623 * 2 ^ 59
def prefixEnd_543623 : Nat := 4983230072969 + 3 ^ 40 * 543623 * 2
def baseEnd_543623 : Nat := 248124350079317161077715

theorem tailTrace_543623 : CollatzResearch.WordTrace tailWord_543623 prefixEnd_543623 248124350079317161077715 := by
  unfold tailWord_543623
  simp only [CollatzResearch.WordTrace]
  refine ⟨19827559709554189261867523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13218373139702792841245015 19827559709554189261867523)
  ·
    refine ⟨29741339564331283892801285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19827559709554189261867523 29741339564331283892801285)
    ·
      refine ⟨5576501168312115729900241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29741339564331283892801285 5576501168312115729900241)
      ·
        refine ⟨4182375876234086797425181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5576501168312115729900241 4182375876234086797425181)
        ·
          refine ⟨1568390953587782549034443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4182375876234086797425181 1568390953587782549034443)
          ·
            refine ⟨2352586430381673823551665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568390953587782549034443 2352586430381673823551665)
            ·
              refine ⟨1764439822786255367663749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352586430381673823551665 1764439822786255367663749)
              ·
                refine ⟨330832466772422881436953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1764439822786255367663749 330832466772422881436953)
                ·
                  refine ⟨248124350079317161077715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330832466772422881436953 248124350079317161077715)
                  ·
                    rfl

theorem cell20_543623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2].length) (baseStart_543623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543623 prefixEnd_543623 := by exact prefixLift 543623
  have htrace : WordTrace (prefixWord ++ tailWord_543623) baseStart_543623 baseEnd_543623 := by
    simpa [prefixWord, tailWord_543623, baseEnd_543623] using wordTrace_append hprefix tailTrace_543623
  have hstable : (prefixWord ++ tailWord_543623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543623).length < 2 ^ (prefixWord ++ tailWord_543623).sum := by decide
  have hdescent : baseEnd_543623 < baseStart_543623 := by decide
  rcases family_descends (prefixWord ++ tailWord_543623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543627 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_543627 : Nat := 118140960795 + 543627 * 2 ^ 59
def prefixEnd_543627 : Nat := 4983230072969 + 3 ^ 40 * 543627 * 2
def baseEnd_543627 : Nat := 248126175788310924944365

theorem tailTrace_543627 : CollatzResearch.WordTrace tailWord_543627 prefixEnd_543627 248126175788310924944365 := by
  unfold tailWord_543627
  simp only [CollatzResearch.WordTrace]
  refine ⟨19827705601539697945013135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13218470401026465296675423 19827705601539697945013135)
  ·
    refine ⟨29741558402309546917519703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19827705601539697945013135 29741558402309546917519703)
    ·
      refine ⟨44612337603464320376279555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29741558402309546917519703 44612337603464320376279555)
      ·
        refine ⟨66918506405196480564419333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44612337603464320376279555 66918506405196480564419333)
        ·
          refine ⟨12547219950974340105828625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66918506405196480564419333 12547219950974340105828625)
          ·
            refine ⟨9410414963230755079371469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12547219950974340105828625 9410414963230755079371469)
            ·
              refine ⟨3528905611211533154764301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9410414963230755079371469 3528905611211533154764301)
              ·
                refine ⟨1323339604204324933036613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3528905611211533154764301 1323339604204324933036613)
                ·
                  refine ⟨248126175788310924944365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323339604204324933036613 248126175788310924944365)
                  ·
                    rfl

theorem cell20_543627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_543627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543627 prefixEnd_543627 := by exact prefixLift 543627
  have htrace : WordTrace (prefixWord ++ tailWord_543627) baseStart_543627 baseEnd_543627 := by
    simpa [prefixWord, tailWord_543627, baseEnd_543627] using wordTrace_append hprefix tailTrace_543627
  have hstable : (prefixWord ++ tailWord_543627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543627).length < 2 ^ (prefixWord ++ tailWord_543627).sum := by decide
  have hdescent : baseEnd_543627 < baseStart_543627 := by decide
  rcases family_descends (prefixWord ++ tailWord_543627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543651 : List Nat := [1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_543651 : Nat := 118140960795 + 543651 * 2 ^ 59
def prefixEnd_543651 : Nat := 4983230072969 + 3 ^ 40 * 543651 * 2
def baseEnd_543651 : Nat := 82712376680757836048089

theorem tailTrace_543651 : CollatzResearch.WordTrace tailWord_543651 prefixEnd_543651 82712376680757836048089 := by
  unfold tailWord_543651
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828580953452750043886807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13219053968968500029257871 19828580953452750043886807)
  ·
    refine ⟨29742871430179125065830211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19828580953452750043886807 29742871430179125065830211)
    ·
      refine ⟨44614307145268687598745317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29742871430179125065830211 44614307145268687598745317)
      ·
        refine ⟨8365182589737878924764747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44614307145268687598745317 8365182589737878924764747)
        ·
          refine ⟨12547773884606818387147121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365182589737878924764747 12547773884606818387147121)
          ·
            refine ⟨9410830413455113790360341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12547773884606818387147121 9410830413455113790360341)
            ·
              refine ⟨441132675630708458923141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9410830413455113790360341 441132675630708458923141)
              ·
                refine ⟨82712376680757836048089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441132675630708458923141 82712376680757836048089)
                ·
                  rfl

theorem cell20_543651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_543651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543651 prefixEnd_543651 := by exact prefixLift 543651
  have htrace : WordTrace (prefixWord ++ tailWord_543651) baseStart_543651 baseEnd_543651 := by
    simpa [prefixWord, tailWord_543651, baseEnd_543651] using wordTrace_append hprefix tailTrace_543651
  have hstable : (prefixWord ++ tailWord_543651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543651).length < 2 ^ (prefixWord ++ tailWord_543651).sum := by decide
  have hdescent : baseEnd_543651 < baseStart_543651 := by decide
  rcases family_descends (prefixWord ++ tailWord_543651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543668 : List Nat := [2, 5, 2, 1, 1, 1, 8]
def baseStart_543668 : Nat := 118140960795 + 543668 * 2 ^ 59
def prefixEnd_543668 : Nat := 4983230072969 + 3 ^ 40 * 543668 * 2
def baseEnd_543668 : Nat := 27571654367277444953059

theorem tailTrace_543668 : CollatzResearch.WordTrace tailWord_543668 prefixEnd_543668 27571654367277444953059 := by
  unfold tailWord_543668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914600497195580973627829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13219467329594107964837105 9914600497195580973627829)
  ·
    refine ⟨929493796612085716277609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9914600497195580973627829 929493796612085716277609)
    ·
      refine ⟨697120347459064287208207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929493796612085716277609 697120347459064287208207)
      ·
        refine ⟨1045680521188596430812311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697120347459064287208207 1045680521188596430812311)
        ·
          refine ⟨1568520781782894646218467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045680521188596430812311 1568520781782894646218467)
          ·
            refine ⟨2352781172674341969327701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568520781782894646218467 2352781172674341969327701)
            ·
              refine ⟨27571654367277444953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2352781172674341969327701 27571654367277444953059)
              ·
                rfl

theorem cell20_543668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_543668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543668 prefixEnd_543668 := by exact prefixLift 543668
  have htrace : WordTrace (prefixWord ++ tailWord_543668) baseStart_543668 baseEnd_543668 := by
    simpa [prefixWord, tailWord_543668, baseEnd_543668] using wordTrace_append hprefix tailTrace_543668
  have hstable : (prefixWord ++ tailWord_543668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543668).length < 2 ^ (prefixWord ++ tailWord_543668).sum := by decide
  have hdescent : baseEnd_543668 < baseStart_543668 := by decide
  rcases family_descends (prefixWord ++ tailWord_543668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543672 : List Nat := [2, 1, 2, 1, 2, 4, 8]
def baseStart_543672 : Nat := 118140960795 + 543672 * 2 ^ 59
def prefixEnd_543672 : Nat := 4983230072969 + 3 ^ 40 * 543672 * 2
def baseEnd_543672 : Nat := 27571857223832307604909

theorem tailTrace_543672 : CollatzResearch.WordTrace tailWord_543672 prefixEnd_543672 27571857223832307604909 := by
  unfold tailWord_543672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914673443188335315200635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13219564590917780420267513 9914673443188335315200635)
  ·
    refine ⟨14872010164782502972800953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9914673443188335315200635 14872010164782502972800953)
    ·
      refine ⟨11154007623586877229600715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14872010164782502972800953 11154007623586877229600715)
      ·
        refine ⟨16731011435380315844401073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154007623586877229600715 16731011435380315844401073)
        ·
          refine ⟨12548258576535236883300805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16731011435380315844401073 12548258576535236883300805)
          ·
            refine ⟨2352798483100356915618901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12548258576535236883300805 2352798483100356915618901)
            ·
              refine ⟨27571857223832307604909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2352798483100356915618901 27571857223832307604909)
              ·
                rfl

theorem cell20_543672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_543672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543672 prefixEnd_543672 := by exact prefixLift 543672
  have htrace : WordTrace (prefixWord ++ tailWord_543672) baseStart_543672 baseEnd_543672 := by
    simpa [prefixWord, tailWord_543672, baseEnd_543672] using wordTrace_append hprefix tailTrace_543672
  have hstable : (prefixWord ++ tailWord_543672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543672).length < 2 ^ (prefixWord ++ tailWord_543672).sum := by decide
  have hdescent : baseEnd_543672 < baseStart_543672 := by decide
  rcases family_descends (prefixWord ++ tailWord_543672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543678 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_543678 : Nat := 118140960795 + 543678 * 2 ^ 59
def prefixEnd_543678 : Nat := 4983230072969 + 3 ^ 40 * 543678 * 2
def baseEnd_543678 : Nat := 248149453577981414244157

theorem tailTrace_543678 : CollatzResearch.WordTrace tailWord_543678 prefixEnd_543678 248149453577981414244157 := by
  unfold tailWord_543678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478695715544366706889961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13219710482903289103413125 2478695715544366706889961)
  ·
    refine ⟨1859021786658275030167471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2478695715544366706889961 1859021786658275030167471)
    ·
      refine ⟨2788532679987412545251207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859021786658275030167471 2788532679987412545251207)
      ·
        refine ⟨4182799019981118817876811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788532679987412545251207 4182799019981118817876811)
        ·
          refine ⟨6274198529971678226815217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182799019981118817876811 6274198529971678226815217)
          ·
            refine ⟨4705648897478758670111413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274198529971678226815217 4705648897478758670111413)
            ·
              refine ⟨441154584138633625322945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4705648897478758670111413 441154584138633625322945)
              ·
                refine ⟨330865938103975218992209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441154584138633625322945 330865938103975218992209)
                ·
                  refine ⟨248149453577981414244157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330865938103975218992209 248149453577981414244157)
                  ·
                    rfl

theorem cell20_543678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_543678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543678 prefixEnd_543678 := by exact prefixLift 543678
  have htrace : WordTrace (prefixWord ++ tailWord_543678) baseStart_543678 baseEnd_543678 := by
    simpa [prefixWord, tailWord_543678, baseEnd_543678] using wordTrace_append hprefix tailTrace_543678
  have hstable : (prefixWord ++ tailWord_543678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543678).length < 2 ^ (prefixWord ++ tailWord_543678).sum := by decide
  have hdescent : baseEnd_543678 < baseStart_543678 := by decide
  rcases family_descends (prefixWord ++ tailWord_543678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543733 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 2]
def baseStart_543733 : Nat := 118140960795 + 543733 * 2 ^ 59
def prefixEnd_543733 : Nat := 4983230072969 + 3 ^ 40 * 543733 * 2
def baseEnd_543733 : Nat := 248174557076645667410599

theorem tailTrace_543733 : CollatzResearch.WordTrace tailWord_543733 prefixEnd_543733 248174557076645667410599 := by
  unfold tailWord_543733
  simp only [CollatzResearch.WordTrace]
  refine ⟨19831571739155678048371853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13221047826103785365581235 19831571739155678048371853)
  ·
    refine ⟨7436839402183379268139445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19831571739155678048371853 7436839402183379268139445)
    ·
      refine ⟨697203693954691806388073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7436839402183379268139445 697203693954691806388073)
      ·
        refine ⟨522902770466018854791055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 697203693954691806388073 522902770466018854791055)
        ·
          refine ⟨784354155699028282186583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522902770466018854791055 784354155699028282186583)
          ·
            refine ⟨1176531233548542423279875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784354155699028282186583 1176531233548542423279875)
            ·
              refine ⟨1764796850322813634919813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176531233548542423279875 1764796850322813634919813)
              ·
                refine ⟨330899409435527556547465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1764796850322813634919813 330899409435527556547465)
                ·
                  refine ⟨248174557076645667410599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330899409435527556547465 248174557076645667410599)
                  ·
                    rfl

theorem cell20_543733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_543733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543733 prefixEnd_543733 := by exact prefixLift 543733
  have htrace : WordTrace (prefixWord ++ tailWord_543733) baseStart_543733 baseEnd_543733 := by
    simpa [prefixWord, tailWord_543733, baseEnd_543733] using wordTrace_append hprefix tailTrace_543733
  have hstable : (prefixWord ++ tailWord_543733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543733).length < 2 ^ (prefixWord ++ tailWord_543733).sum := by decide
  have hdescent : baseEnd_543733 < baseStart_543733 := by decide
  rcases family_descends (prefixWord ++ tailWord_543733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543741 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_543741 : Nat := 118140960795 + 543741 * 2 ^ 59
def prefixEnd_543741 : Nat := 4983230072969 + 3 ^ 40 * 543741 * 2
def baseEnd_543741 : Nat := 248178208494633195143899

theorem tailTrace_543741 : CollatzResearch.WordTrace tailWord_543741 prefixEnd_543741 248178208494633195143899 := by
  unfold tailWord_543741
  simp only [CollatzResearch.WordTrace]
  refine ⟨19831863523126695414663077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13221242348751130276442051 19831863523126695414663077)
  ·
    refine ⟨3718474410586255390249327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19831863523126695414663077 3718474410586255390249327)
    ·
      refine ⟨5577711615879383085373991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718474410586255390249327 5577711615879383085373991)
      ·
        refine ⟨8366567423819074628060987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577711615879383085373991 8366567423819074628060987)
        ·
          refine ⟨12549851135728611942091481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366567423819074628060987 12549851135728611942091481)
          ·
            refine ⟨9412388351796458956568611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12549851135728611942091481 9412388351796458956568611)
            ·
              refine ⟨14118582527694688434852917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412388351796458956568611 14118582527694688434852917)
              ·
                refine ⟨1323617111971377040767461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14118582527694688434852917 1323617111971377040767461)
                ·
                  refine ⟨248178208494633195143899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323617111971377040767461 248178208494633195143899)
                  ·
                    rfl

theorem cell20_543741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_543741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543741 prefixEnd_543741 := by exact prefixLift 543741
  have htrace : WordTrace (prefixWord ++ tailWord_543741) baseStart_543741 baseEnd_543741 := by
    simpa [prefixWord, tailWord_543741, baseEnd_543741] using wordTrace_append hprefix tailTrace_543741
  have hstable : (prefixWord ++ tailWord_543741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543741).length < 2 ^ (prefixWord ++ tailWord_543741).sum := by decide
  have hdescent : baseEnd_543741 < baseStart_543741 := by decide
  rcases family_descends (prefixWord ++ tailWord_543741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543758 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_543758 : Nat := 118140960795 + 543758 * 2 ^ 59
def prefixEnd_543758 : Nat := 4983230072969 + 3 ^ 40 * 543758 * 2
def baseEnd_543758 : Nat := 248185967757856691577163

theorem tailTrace_543758 : CollatzResearch.WordTrace tailWord_543758 prefixEnd_543758 248185967757856691577163 := by
  unfold tailWord_543758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479060445508138414753991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13221655709376738212021285 2479060445508138414753991)
  ·
    refine ⟨3718590668262207622130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479060445508138414753991 3718590668262207622130987)
    ·
      refine ⟨5577886002393311433196481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718590668262207622130987 5577886002393311433196481)
      ·
        refine ⟨4183414501794983574897361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5577886002393311433196481 4183414501794983574897361)
        ·
          refine ⟨3137560876346237681173021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4183414501794983574897361 3137560876346237681173021)
          ·
            refine ⟨1176585328629839130439883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3137560876346237681173021 1176585328629839130439883)
            ·
              refine ⟨1764877992944758695659825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176585328629839130439883 1764877992944758695659825)
              ·
                refine ⟨1323658494708569021744869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764877992944758695659825 1323658494708569021744869)
                ·
                  refine ⟨248185967757856691577163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323658494708569021744869 248185967757856691577163)
                  ·
                    rfl

theorem cell20_543758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_543758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543758 prefixEnd_543758 := by exact prefixLift 543758
  have htrace : WordTrace (prefixWord ++ tailWord_543758) baseStart_543758 baseEnd_543758 := by
    simpa [prefixWord, tailWord_543758, baseEnd_543758] using wordTrace_append hprefix tailTrace_543758
  have hstable : (prefixWord ++ tailWord_543758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543758).length < 2 ^ (prefixWord ++ tailWord_543758).sum := by decide
  have hdescent : baseEnd_543758 < baseStart_543758 := by decide
  rcases family_descends (prefixWord ++ tailWord_543758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543775 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 2]
def baseStart_543775 : Nat := 118140960795 + 543775 * 2 ^ 59
def prefixEnd_543775 : Nat := 4983230072969 + 3 ^ 40 * 543775 * 2
def baseEnd_543775 : Nat := 248193727021080188010427

theorem tailTrace_543775 : CollatzResearch.WordTrace tailWord_543775 prefixEnd_543775 248193727021080188010427 := by
  unfold tailWord_543775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19833103605003519221400779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13222069070002346147600519 19833103605003519221400779)
  ·
    refine ⟨29749655407505278832101169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19833103605003519221400779 29749655407505278832101169)
    ·
      refine ⟨22312241555628959124075877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29749655407505278832101169 22312241555628959124075877)
      ·
        refine ⟨4183545291680429835764227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22312241555628959124075877 4183545291680429835764227)
        ·
          refine ⟨6275317937520644753646341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183545291680429835764227 6275317937520644753646341)
          ·
            refine ⟨1176622113285120891308689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6275317937520644753646341 1176622113285120891308689)
            ·
              refine ⟨882466584963840668481517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176622113285120891308689 882466584963840668481517)
              ·
                refine ⟨330924969361440250680569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 882466584963840668481517 330924969361440250680569)
                ·
                  refine ⟨248193727021080188010427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330924969361440250680569 248193727021080188010427)
                  ·
                    rfl

theorem cell20_543775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 2].length) (baseStart_543775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543775 prefixEnd_543775 := by exact prefixLift 543775
  have htrace : WordTrace (prefixWord ++ tailWord_543775) baseStart_543775 baseEnd_543775 := by
    simpa [prefixWord, tailWord_543775, baseEnd_543775] using wordTrace_append hprefix tailTrace_543775
  have hstable : (prefixWord ++ tailWord_543775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543775).length < 2 ^ (prefixWord ++ tailWord_543775).sum := by decide
  have hdescent : baseEnd_543775 < baseStart_543775 := by decide
  rcases family_descends (prefixWord ++ tailWord_543775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543834 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_543834 : Nat := 118140960795 + 543834 * 2 ^ 59
def prefixEnd_543834 : Nat := 4983230072969 + 3 ^ 40 * 543834 * 2
def baseEnd_543834 : Nat := 248220656228738205043519

theorem tailTrace_543834 : CollatzResearch.WordTrace tailWord_543834 prefixEnd_543834 248220656228738205043519 := by
  unfold tailWord_543834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958813877947443074449639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13223503674526514865199037 4958813877947443074449639)
  ·
    refine ⟨7438220816921164611674459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958813877947443074449639 7438220816921164611674459)
    ·
      refine ⟨11157331225381746917511689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438220816921164611674459 11157331225381746917511689)
      ·
        refine ⟨8367998419036310188133767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11157331225381746917511689 8367998419036310188133767)
        ·
          refine ⟨12551997628554465282200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367998419036310188133767 12551997628554465282200651)
          ·
            refine ⟨18827996442831697923300977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12551997628554465282200651 18827996442831697923300977)
            ·
              refine ⟨14120997332123773442475733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18827996442831697923300977 14120997332123773442475733)
              ·
                refine ⟨330960874971650940058025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14120997332123773442475733 330960874971650940058025)
                ·
                  refine ⟨248220656228738205043519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330960874971650940058025 248220656228738205043519)
                  ·
                    rfl

theorem cell20_543834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_543834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543834 prefixEnd_543834 := by exact prefixLift 543834
  have htrace : WordTrace (prefixWord ++ tailWord_543834) baseStart_543834 baseEnd_543834 := by
    simpa [prefixWord, tailWord_543834, baseEnd_543834] using wordTrace_append hprefix tailTrace_543834
  have hstable : (prefixWord ++ tailWord_543834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543834).length < 2 ^ (prefixWord ++ tailWord_543834).sum := by decide
  have hdescent : baseEnd_543834 < baseStart_543834 := by decide
  rcases family_descends (prefixWord ++ tailWord_543834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543837 : List Nat := [1, 4, 4, 1, 3, 1, 6]
def baseStart_543837 : Nat := 118140960795 + 543837 * 2 ^ 59
def prefixEnd_543837 : Nat := 4983230072969 + 3 ^ 40 * 543837 * 2
def baseEnd_543837 : Nat := 27580225056720391993723

theorem tailTrace_543837 : CollatzResearch.WordTrace tailWord_543837 prefixEnd_543837 27580225056720391993723 := by
  unfold tailWord_543837
  simp only [CollatzResearch.WordTrace]
  refine ⟨19835364930778903810157765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13223576620519269206771843 19835364930778903810157765)
  ·
    refine ⟨3719130924521044464404581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19835364930778903810157765 3719130924521044464404581)
    ·
      refine ⟨697337048347695837075859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3719130924521044464404581 697337048347695837075859)
      ·
        refine ⟨1046005572521543755613789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697337048347695837075859 1046005572521543755613789)
        ·
          refine ⟨392252089695578908355171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046005572521543755613789 392252089695578908355171)
          ·
            refine ⟨588378134543368362532757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392252089695578908355171 588378134543368362532757)
            ·
              refine ⟨27580225056720391993723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 588378134543368362532757 27580225056720391993723)
              ·
                rfl

theorem cell20_543837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_543837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543837 prefixEnd_543837 := by exact prefixLift 543837
  have htrace : WordTrace (prefixWord ++ tailWord_543837) baseStart_543837 baseEnd_543837 := by
    simpa [prefixWord, tailWord_543837, baseEnd_543837] using wordTrace_append hprefix tailTrace_543837
  have hstable : (prefixWord ++ tailWord_543837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543837).length < 2 ^ (prefixWord ++ tailWord_543837).sum := by decide
  have hdescent : baseEnd_543837 < baseStart_543837 := by decide
  rcases family_descends (prefixWord ++ tailWord_543837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543865 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_543865 : Nat := 118140960795 + 543865 * 2 ^ 59
def prefixEnd_543865 : Nat := 4983230072969 + 3 ^ 40 * 543865 * 2
def baseEnd_543865 : Nat := 248234805473439875010059

theorem tailTrace_543865 : CollatzResearch.WordTrace tailWord_543865 prefixEnd_543865 248234805473439875010059 := by
  unfold tailWord_543865
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836386174677464592177049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13224257449784976394784699 19836386174677464592177049)
  ·
    refine ⟨14877289631008098444132787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836386174677464592177049 14877289631008098444132787)
    ·
      refine ⟨22315934446512147666199181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877289631008098444132787 22315934446512147666199181)
      ·
        refine ⟨8368475417442055374824693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22315934446512147666199181 8368475417442055374824693)
        ·
          refine ⟨784544570385192691389815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8368475417442055374824693 784544570385192691389815)
          ·
            refine ⟨1176816855577789037084723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784544570385192691389815 1176816855577789037084723)
            ·
              refine ⟨1765225283366683555627085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176816855577789037084723 1765225283366683555627085)
              ·
                refine ⟨661959481262506333360157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1765225283366683555627085 661959481262506333360157)
                ·
                  refine ⟨248234805473439875010059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661959481262506333360157 248234805473439875010059)
                  ·
                    rfl

theorem cell20_543865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_543865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543865 prefixEnd_543865 := by exact prefixLift 543865
  have htrace : WordTrace (prefixWord ++ tailWord_543865) baseStart_543865 baseEnd_543865 := by
    simpa [prefixWord, tailWord_543865, baseEnd_543865] using wordTrace_append hprefix tailTrace_543865
  have hstable : (prefixWord ++ tailWord_543865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543865).length < 2 ^ (prefixWord ++ tailWord_543865).sum := by decide
  have hdescent : baseEnd_543865 < baseStart_543865 := by decide
  rcases family_descends (prefixWord ++ tailWord_543865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543900 : List Nat := [2, 2, 3, 2, 1, 10]
def baseStart_543900 : Nat := 118140960795 + 543900 * 2 ^ 59
def prefixEnd_543900 : Nat := 4983230072969 + 3 ^ 40 * 543900 * 2
def baseEnd_543900 : Nat := 9194473349153159586787

theorem tailTrace_543900 : CollatzResearch.WordTrace tailWord_543900 prefixEnd_543900 9194473349153159586787 := by
  unfold tailWord_543900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918831364775332784850577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13225108486367110379800769 9918831364775332784850577)
  ·
    refine ⟨7439123523581499588637933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9918831364775332784850577 7439123523581499588637933)
    ·
      refine ⟨2789671321343062345739225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7439123523581499588637933 2789671321343062345739225)
      ·
        refine ⟨2092253491007296759304419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789671321343062345739225 2092253491007296759304419)
        ·
          refine ⟨3138380236510945138956629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092253491007296759304419 3138380236510945138956629)
          ·
            refine ⟨9194473349153159586787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3138380236510945138956629 9194473349153159586787)
            ·
              rfl

theorem cell20_543900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 10].length) (baseStart_543900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543900 prefixEnd_543900 := by exact prefixLift 543900
  have htrace : WordTrace (prefixWord ++ tailWord_543900) baseStart_543900 baseEnd_543900 := by
    simpa [prefixWord, tailWord_543900, baseEnd_543900] using wordTrace_append hprefix tailTrace_543900
  have hstable : (prefixWord ++ tailWord_543900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543900).length < 2 ^ (prefixWord ++ tailWord_543900).sum := by decide
  have hdescent : baseEnd_543900 < baseStart_543900 := by decide
  rcases family_descends (prefixWord ++ tailWord_543900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543906 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_543906 : Nat := 118140960795 + 543906 * 2 ^ 59
def prefixEnd_543906 : Nat := 4983230072969 + 3 ^ 40 * 543906 * 2
def baseEnd_543906 : Nat := 248253518990625954643225

theorem tailTrace_543906 : CollatzResearch.WordTrace tailWord_543906 prefixEnd_543906 248253518990625954643225 := by
  unfold tailWord_543906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959470391882232148604893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13225254378352619062946381 4959470391882232148604893)
  ·
    refine ⟨1859801396955837055726835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4959470391882232148604893 1859801396955837055726835)
    ·
      refine ⟨2789702095433755583590253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859801396955837055726835 2789702095433755583590253)
      ·
        refine ⟨1046138285787658343846345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2789702095433755583590253 1046138285787658343846345)
        ·
          refine ⟨784603714340743757884759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046138285787658343846345 784603714340743757884759)
          ·
            refine ⟨1176905571511115636827139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784603714340743757884759 1176905571511115636827139)
            ·
              refine ⟨1765358357266673455240709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176905571511115636827139 1765358357266673455240709)
              ·
                refine ⟨331004691987501272857633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1765358357266673455240709 331004691987501272857633)
                ·
                  refine ⟨248253518990625954643225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331004691987501272857633 248253518990625954643225)
                  ·
                    rfl

theorem cell20_543906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_543906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543906 prefixEnd_543906 := by exact prefixLift 543906
  have htrace : WordTrace (prefixWord ++ tailWord_543906) baseStart_543906 baseEnd_543906 := by
    simpa [prefixWord, tailWord_543906, baseEnd_543906] using wordTrace_append hprefix tailTrace_543906
  have hstable : (prefixWord ++ tailWord_543906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543906).length < 2 ^ (prefixWord ++ tailWord_543906).sum := by decide
  have hdescent : baseEnd_543906 < baseStart_543906 := by decide
  rcases family_descends (prefixWord ++ tailWord_543906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543907 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_543907 : Nat := 118140960795 + 543907 * 2 ^ 59
def prefixEnd_543907 : Nat := 4983230072969 + 3 ^ 40 * 543907 * 2
def baseEnd_543907 : Nat := 248253975417874395609887

theorem tailTrace_543907 : CollatzResearch.WordTrace tailWord_543907 prefixEnd_543907 248253975417874395609887 := by
  unfold tailWord_543907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19837918040525305765205975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13225278693683537176803983 19837918040525305765205975)
  ·
    refine ⟨29756877060787958647808963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19837918040525305765205975 29756877060787958647808963)
    ·
      refine ⟨44635315591181937971713445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29756877060787958647808963 44635315591181937971713445)
      ·
        refine ⟨8369121673346613369696271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44635315591181937971713445 8369121673346613369696271)
        ·
          refine ⟨12553682510019920054544407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8369121673346613369696271 12553682510019920054544407)
          ·
            refine ⟨18830523765029880081816611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553682510019920054544407 18830523765029880081816611)
            ·
              refine ⟨28245785647544820122724917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18830523765029880081816611 28245785647544820122724917)
              ·
                refine ⟨2648042404457326886505461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28245785647544820122724917 2648042404457326886505461)
                ·
                  refine ⟨248253975417874395609887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2648042404457326886505461 248253975417874395609887)
                  ·
                    rfl

theorem cell20_543907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_543907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543907 prefixEnd_543907 := by exact prefixLift 543907
  have htrace : WordTrace (prefixWord ++ tailWord_543907) baseStart_543907 baseEnd_543907 := by
    simpa [prefixWord, tailWord_543907, baseEnd_543907] using wordTrace_append hprefix tailTrace_543907
  have hstable : (prefixWord ++ tailWord_543907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543907).length < 2 ^ (prefixWord ++ tailWord_543907).sum := by decide
  have hdescent : baseEnd_543907 < baseStart_543907 := by decide
  rcases family_descends (prefixWord ++ tailWord_543907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543934 : List Nat := [4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_543934 : Nat := 118140960795 + 543934 * 2 ^ 59
def prefixEnd_543934 : Nat := 4983230072969 + 3 ^ 40 * 543934 * 2
def baseEnd_543934 : Nat := 82755432984527433903259

theorem tailTrace_543934 : CollatzResearch.WordTrace tailWord_543934 prefixEnd_543934 82755432984527433903259 := by
  unfold tailWord_543934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479862851428436172054857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13225935207618326250959237 2479862851428436172054857)
  ·
    refine ⟨1859897138571327129041143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2479862851428436172054857 1859897138571327129041143)
    ·
      refine ⟨2789845707856990693561715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859897138571327129041143 2789845707856990693561715)
      ·
        refine ⟨4184768561785486040342573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789845707856990693561715 4184768561785486040342573)
        ·
          refine ⟨1569288210669557265128465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4184768561785486040342573 1569288210669557265128465)
          ·
            refine ⟨1176966158002167948846349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569288210669557265128465 1176966158002167948846349)
            ·
              refine ⟨441362309250812980817381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1176966158002167948846349 441362309250812980817381)
              ·
                refine ⟨82755432984527433903259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441362309250812980817381 82755432984527433903259)
                ·
                  rfl

theorem cell20_543934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_543934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543934 prefixEnd_543934 := by exact prefixLift 543934
  have htrace : WordTrace (prefixWord ++ tailWord_543934) baseStart_543934 baseEnd_543934 := by
    simpa [prefixWord, tailWord_543934, baseEnd_543934] using wordTrace_append hprefix tailTrace_543934
  have hstable : (prefixWord ++ tailWord_543934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543934).length < 2 ^ (prefixWord ++ tailWord_543934).sum := by decide
  have hdescent : baseEnd_543934 < baseStart_543934 := by decide
  rcases family_descends (prefixWord ++ tailWord_543934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543958 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_543958 : Nat := 118140960795 + 543958 * 2 ^ 59
def prefixEnd_543958 : Nat := 4983230072969 + 3 ^ 40 * 543958 * 2
def baseEnd_543958 : Nat := 248277253207544884909679

theorem tailTrace_543958 : CollatzResearch.WordTrace tailWord_543958 prefixEnd_543958 248277253207544884909679 := by
  unfold tailWord_543958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239986135208783842207033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13226518775560360983541685 1239986135208783842207033)
  ·
    refine ⟨929989601406587881655275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239986135208783842207033 929989601406587881655275)
    ·
      refine ⟨1394984402109881822482913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929989601406587881655275 1394984402109881822482913)
      ·
        refine ⟨1046238301582411366862185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394984402109881822482913 1046238301582411366862185)
        ·
          refine ⟨784678726186808525146639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046238301582411366862185 784678726186808525146639)
          ·
            refine ⟨1177018089280212787719959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784678726186808525146639 1177018089280212787719959)
            ·
              refine ⟨1765527133920319181579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177018089280212787719959 1765527133920319181579939)
              ·
                refine ⟨2648290700880478772369909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765527133920319181579939 2648290700880478772369909)
                ·
                  refine ⟨248277253207544884909679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2648290700880478772369909 248277253207544884909679)
                  ·
                    rfl

theorem cell20_543958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_543958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543958 prefixEnd_543958 := by exact prefixLift 543958
  have htrace : WordTrace (prefixWord ++ tailWord_543958) baseStart_543958 baseEnd_543958 := by
    simpa [prefixWord, tailWord_543958, baseEnd_543958] using wordTrace_append hprefix tailTrace_543958
  have hstable : (prefixWord ++ tailWord_543958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543958).length < 2 ^ (prefixWord ++ tailWord_543958).sum := by decide
  have hdescent : baseEnd_543958 < baseStart_543958 := by decide
  rcases family_descends (prefixWord ++ tailWord_543958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543965 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_543965 : Nat := 118140960795 + 543965 * 2 ^ 59
def prefixEnd_543965 : Nat := 4983230072969 + 3 ^ 40 * 543965 * 2
def baseEnd_543965 : Nat := 248280448198283971676317

theorem tailTrace_543965 : CollatzResearch.WordTrace tailWord_543965 prefixEnd_543965 248280448198283971676317 := by
  unfold tailWord_543965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840033474315181670817349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13226688982876787780544899 19840033474315181670817349)
  ·
    refine ⟨3720006276434096563278253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19840033474315181670817349 3720006276434096563278253)
    ·
      refine ⟨1395002353662786211229345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3720006276434096563278253 1395002353662786211229345)
      ·
        refine ⟨1046251765247089658422009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395002353662786211229345 1046251765247089658422009)
        ·
          refine ⟨784688823935317243816507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046251765247089658422009 784688823935317243816507)
          ·
            refine ⟨1177033235902975865724761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784688823935317243816507 1177033235902975865724761)
            ·
              refine ⟨882774926927231899293571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177033235902975865724761 882774926927231899293571)
              ·
                refine ⟨1324162390390847848940357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882774926927231899293571 1324162390390847848940357)
                ·
                  refine ⟨248280448198283971676317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324162390390847848940357 248280448198283971676317)
                  ·
                    rfl

theorem cell20_543965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_543965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543965 prefixEnd_543965 := by exact prefixLift 543965
  have htrace : WordTrace (prefixWord ++ tailWord_543965) baseStart_543965 baseEnd_543965 := by
    simpa [prefixWord, tailWord_543965, baseEnd_543965] using wordTrace_append hprefix tailTrace_543965
  have hstable : (prefixWord ++ tailWord_543965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543965).length < 2 ^ (prefixWord ++ tailWord_543965).sum := by decide
  have hdescent : baseEnd_543965 < baseStart_543965 := by decide
  rcases family_descends (prefixWord ++ tailWord_543965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543969 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_543969 : Nat := 118140960795 + 543969 * 2 ^ 59
def prefixEnd_543969 : Nat := 4983230072969 + 3 ^ 40 * 543969 * 2
def baseEnd_543969 : Nat := 248282273907277735542967

theorem tailTrace_543969 : CollatzResearch.WordTrace tailWord_543969 prefixEnd_543969 248282273907277735542967 := by
  unfold tailWord_543969
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840179366300690353962961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13226786244200460235975307 19840179366300690353962961)
  ·
    refine ⟨14880134524725517765472221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19840179366300690353962961 14880134524725517765472221)
    ·
      refine ⟨5580050446772069162052083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14880134524725517765472221 5580050446772069162052083)
      ·
        refine ⟨8370075670158103743078125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580050446772069162052083 8370075670158103743078125)
        ·
          refine ⟨3138778376309288903654297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8370075670158103743078125 3138778376309288903654297)
          ·
            refine ⟨2354083782231966677740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138778376309288903654297 2354083782231966677740723)
            ·
              refine ⟨3531125673347950016611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354083782231966677740723 3531125673347950016611085)
              ·
                refine ⟨1324172127505481256229157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3531125673347950016611085 1324172127505481256229157)
                ·
                  refine ⟨248282273907277735542967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324172127505481256229157 248282273907277735542967)
                  ·
                    rfl

theorem cell20_543969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_543969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543969 prefixEnd_543969 := by exact prefixLift 543969
  have htrace : WordTrace (prefixWord ++ tailWord_543969) baseStart_543969 baseEnd_543969 := by
    simpa [prefixWord, tailWord_543969, baseEnd_543969] using wordTrace_append hprefix tailTrace_543969
  have hstable : (prefixWord ++ tailWord_543969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543969).length < 2 ^ (prefixWord ++ tailWord_543969).sum := by decide
  have hdescent : baseEnd_543969 < baseStart_543969 := by decide
  rcases family_descends (prefixWord ++ tailWord_543969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543976 : List Nat := [2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_543976 : Nat := 118140960795 + 543976 * 2 ^ 59
def prefixEnd_543976 : Nat := 4983230072969 + 3 ^ 40 * 543976 * 2
def baseEnd_543976 : Nat := 82761822966005607436535

theorem tailTrace_543976 : CollatzResearch.WordTrace tailWord_543976 prefixEnd_543976 82761822966005607436535 := by
  unfold tailWord_543976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9920217338637665274733891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13226956451516887032978521 9920217338637665274733891)
  ·
    refine ⟨14880326007956497912100837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9920217338637665274733891 14880326007956497912100837)
    ·
      refine ⟨2790061126491843358518907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14880326007956497912100837 2790061126491843358518907)
      ·
        refine ⟨4185091689737765037778361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790061126491843358518907 4185091689737765037778361)
        ·
          refine ⟨3138818767303323778333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4185091689737765037778361 3138818767303323778333771)
          ·
            refine ⟨4708228150954985667500657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138818767303323778333771 4708228150954985667500657)
            ·
              refine ⟨3531171113216239250625493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4708228150954985667500657 3531171113216239250625493)
              ·
                refine ⟨82761822966005607436535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3531171113216239250625493 82761822966005607436535)
                ·
                  rfl

theorem cell20_543976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_543976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543976 prefixEnd_543976 := by exact prefixLift 543976
  have htrace : WordTrace (prefixWord ++ tailWord_543976) baseStart_543976 baseEnd_543976 := by
    simpa [prefixWord, tailWord_543976, baseEnd_543976] using wordTrace_append hprefix tailTrace_543976
  have hstable : (prefixWord ++ tailWord_543976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543976).length < 2 ^ (prefixWord ++ tailWord_543976).sum := by decide
  have hdescent : baseEnd_543976 < baseStart_543976 := by decide
  rcases family_descends (prefixWord ++ tailWord_543976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_543979 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_543979 : Nat := 118140960795 + 543979 * 2 ^ 59
def prefixEnd_543979 : Nat := 4983230072969 + 3 ^ 40 * 543979 * 2
def baseEnd_543979 : Nat := 248286838179762145209593

theorem tailTrace_543979 : CollatzResearch.WordTrace tailWord_543979 prefixEnd_543979 248286838179762145209593 := by
  unfold tailWord_543979
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840544096264462061826991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13227029397509641374551327 19840544096264462061826991)
  ·
    refine ⟨29760816144396693092740487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19840544096264462061826991 29760816144396693092740487)
    ·
      refine ⟨44641224216595039639110731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29760816144396693092740487 44641224216595039639110731)
      ·
        refine ⟨66961836324892559458666097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44641224216595039639110731 66961836324892559458666097)
        ·
          refine ⟨50221377243669419593999573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66961836324892559458666097 50221377243669419593999573)
          ·
            refine ⟨1177063529148502021734365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50221377243669419593999573 1177063529148502021734365)
            ·
              refine ⟨441398823430688258150387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177063529148502021734365 441398823430688258150387)
              ·
                refine ⟨662098235146032387225581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441398823430688258150387 662098235146032387225581)
                ·
                  refine ⟨248286838179762145209593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662098235146032387225581 248286838179762145209593)
                  ·
                    rfl

theorem cell20_543979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_543979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_543979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_543979 prefixEnd_543979 := by exact prefixLift 543979
  have htrace : WordTrace (prefixWord ++ tailWord_543979) baseStart_543979 baseEnd_543979 := by
    simpa [prefixWord, tailWord_543979, baseEnd_543979] using wordTrace_append hprefix tailTrace_543979
  have hstable : (prefixWord ++ tailWord_543979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_543979).length < 2 ^ (prefixWord ++ tailWord_543979).sum := by decide
  have hdescent : baseEnd_543979 < baseStart_543979 := by decide
  rcases family_descends (prefixWord ++ tailWord_543979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544003 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 2]
def baseStart_544003 : Nat := 118140960795 + 544003 * 2 ^ 59
def prefixEnd_544003 : Nat := 4983230072969 + 3 ^ 40 * 544003 * 2
def baseEnd_544003 : Nat := 248297792433724728409495

theorem tailTrace_544003 : CollatzResearch.WordTrace tailWord_544003 prefixEnd_544003 248297792433724728409495 := by
  unfold tailWord_544003
  simp only [CollatzResearch.WordTrace]
  refine ⟨19841419448177514160700663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13227612965451676107133775 19841419448177514160700663)
  ·
    refine ⟨29762129172266271241050995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19841419448177514160700663 29762129172266271241050995)
    ·
      refine ⟨44643193758399406861576493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29762129172266271241050995 44643193758399406861576493)
      ·
        refine ⟨16741197659399777573091185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44643193758399406861576493 16741197659399777573091185)
        ·
          refine ⟨12555898244549833179818389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16741197659399777573091185 12555898244549833179818389)
          ·
            refine ⟨588557730213273430303987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12555898244549833179818389 588557730213273430303987)
            ·
              refine ⟨882836595319910145455981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588557730213273430303987 882836595319910145455981)
              ·
                refine ⟨331063723244966304545993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 882836595319910145455981 331063723244966304545993)
                ·
                  refine ⟨248297792433724728409495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331063723244966304545993 248297792433724728409495)
                  ·
                    rfl

theorem cell20_544003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2].length) (baseStart_544003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544003 prefixEnd_544003 := by exact prefixLift 544003
  have htrace : WordTrace (prefixWord ++ tailWord_544003) baseStart_544003 baseEnd_544003 := by
    simpa [prefixWord, tailWord_544003, baseEnd_544003] using wordTrace_append hprefix tailTrace_544003
  have hstable : (prefixWord ++ tailWord_544003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544003).length < 2 ^ (prefixWord ++ tailWord_544003).sum := by decide
  have hdescent : baseEnd_544003 < baseStart_544003 := by decide
  rcases family_descends (prefixWord ++ tailWord_544003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544014 : List Nat := [4, 1, 1, 2, 1, 3, 8]
def baseStart_544014 : Nat := 118140960795 + 544014 * 2 ^ 59
def prefixEnd_544014 : Nat := 4983230072969 + 3 ^ 40 * 544014 * 2
def baseEnd_544014 : Nat := 27589201459273064338087

theorem tailTrace_544014 : CollatzResearch.WordTrace tailWord_544014 prefixEnd_544014 27589201459273064338087 := by
  unfold tailWord_544014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480227581392207879918887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13227880434091775359567397 2480227581392207879918887)
  ·
    refine ⟨3720341372088311819878331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2480227581392207879918887 3720341372088311819878331)
    ·
      refine ⟨5580512058132467729817497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3720341372088311819878331 5580512058132467729817497)
      ·
        refine ⟨4185384043599350797363123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5580512058132467729817497 4185384043599350797363123)
        ·
          refine ⟨6278076065399026196044685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185384043599350797363123 6278076065399026196044685)
          ·
            refine ⟨2354278524524634823516757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6278076065399026196044685 2354278524524634823516757)
            ·
              refine ⟨27589201459273064338087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2354278524524634823516757 27589201459273064338087)
              ·
                rfl

theorem cell20_544014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_544014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544014 prefixEnd_544014 := by exact prefixLift 544014
  have htrace : WordTrace (prefixWord ++ tailWord_544014) baseStart_544014 baseEnd_544014 := by
    simpa [prefixWord, tailWord_544014, baseEnd_544014] using wordTrace_append hprefix tailTrace_544014
  have hstable : (prefixWord ++ tailWord_544014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544014).length < 2 ^ (prefixWord ++ tailWord_544014).sum := by decide
  have hdescent : baseEnd_544014 < baseStart_544014 := by decide
  rcases family_descends (prefixWord ++ tailWord_544014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544024 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_544024 : Nat := 118140960795 + 544024 * 2 ^ 59
def prefixEnd_544024 : Nat := 4983230072969 + 3 ^ 40 * 544024 * 2
def baseEnd_544024 : Nat := 248307377405941988709409

theorem tailTrace_544024 : CollatzResearch.WordTrace tailWord_544024 prefixEnd_544024 248307377405941988709409 := by
  unfold tailWord_544024
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921092690550717373607563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13228123587400956498143417 9921092690550717373607563)
  ·
    refine ⟨14881639035826076060411345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921092690550717373607563 14881639035826076060411345)
    ·
      refine ⟨11161229276869557045308509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14881639035826076060411345 11161229276869557045308509)
      ·
        refine ⟨4185460978826083891990691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11161229276869557045308509 4185460978826083891990691)
        ·
          refine ⟨6278191468239125837986037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185460978826083891990691 6278191468239125837986037)
          ·
            refine ⟨588580450147418047311191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6278191468239125837986037 588580450147418047311191)
            ·
              refine ⟨882870675221127070966787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588580450147418047311191 882870675221127070966787)
              ·
                refine ⟨1324306012831690606450181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882870675221127070966787 1324306012831690606450181)
                ·
                  refine ⟨248307377405941988709409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324306012831690606450181 248307377405941988709409)
                  ·
                    rfl

theorem cell20_544024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_544024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544024 prefixEnd_544024 := by exact prefixLift 544024
  have htrace : WordTrace (prefixWord ++ tailWord_544024) baseStart_544024 baseEnd_544024 := by
    simpa [prefixWord, tailWord_544024, baseEnd_544024] using wordTrace_append hprefix tailTrace_544024
  have hstable : (prefixWord ++ tailWord_544024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544024).length < 2 ^ (prefixWord ++ tailWord_544024).sum := by decide
  have hdescent : baseEnd_544024 < baseStart_544024 := by decide
  rcases family_descends (prefixWord ++ tailWord_544024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544030 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_544030 : Nat := 118140960795 + 544030 * 2 ^ 59
def prefixEnd_544030 : Nat := 4983230072969 + 3 ^ 40 * 544030 * 2
def baseEnd_544030 : Nat := 248310115969432634509385

theorem tailTrace_544030 : CollatzResearch.WordTrace tailWord_544030 prefixEnd_544030 248310115969432634509385 := by
  unfold tailWord_544030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480300527384962221491693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13228269479386465181289029 2480300527384962221491693)
  ·
    refine ⟨930112697769360833059385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2480300527384962221491693 930112697769360833059385)
    ·
      refine ⟨697584523327020624794539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 930112697769360833059385 697584523327020624794539)
      ·
        refine ⟨1046376784990530937191809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697584523327020624794539 1046376784990530937191809)
        ·
          refine ⟨784782588742898202893857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046376784990530937191809 784782588742898202893857)
          ·
            refine ⟨588586941557173652170393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784782588742898202893857 588586941557173652170393)
            ·
              refine ⟨441440206167880239127795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588586941557173652170393 441440206167880239127795)
              ·
                refine ⟨662160309251820358691693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441440206167880239127795 662160309251820358691693)
                ·
                  refine ⟨248310115969432634509385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662160309251820358691693 248310115969432634509385)
                  ·
                    rfl

theorem cell20_544030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_544030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544030 prefixEnd_544030 := by exact prefixLift 544030
  have htrace : WordTrace (prefixWord ++ tailWord_544030) baseStart_544030 baseEnd_544030 := by
    simpa [prefixWord, tailWord_544030, baseEnd_544030] using wordTrace_append hprefix tailTrace_544030
  have hstable : (prefixWord ++ tailWord_544030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544030).length < 2 ^ (prefixWord ++ tailWord_544030).sum := by decide
  have hdescent : baseEnd_544030 < baseStart_544030 := by decide
  rcases family_descends (prefixWord ++ tailWord_544030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544031 : List Nat := [1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_544031 : Nat := 118140960795 + 544031 * 2 ^ 59
def prefixEnd_544031 : Nat := 4983230072969 + 3 ^ 40 * 544031 * 2
def baseEnd_544031 : Nat := 82770190798893691825349

theorem tailTrace_544031 : CollatzResearch.WordTrace tailWord_544031 prefixEnd_544031 82770190798893691825349 := by
  unfold tailWord_544031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842440692076074942719947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13228293794717383295146631 19842440692076074942719947)
  ·
    refine ⟨29763661038114112414079921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19842440692076074942719947 29763661038114112414079921)
    ·
      refine ⟨22322745778585584310559941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29763661038114112414079921 22322745778585584310559941)
      ·
        refine ⟨4185514833484797058229989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22322745778585584310559941 4185514833484797058229989)
        ·
          refine ⟨784784031278399448418123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4185514833484797058229989 784784031278399448418123)
          ·
            refine ⟨1177176046917599172627185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784784031278399448418123 1177176046917599172627185)
            ·
              refine ⟨882882035188199379470389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177176046917599172627185 882882035188199379470389)
              ·
                refine ⟨82770190798893691825349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 882882035188199379470389 82770190798893691825349)
                ·
                  rfl

theorem cell20_544031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_544031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544031 prefixEnd_544031 := by exact prefixLift 544031
  have htrace : WordTrace (prefixWord ++ tailWord_544031) baseStart_544031 baseEnd_544031 := by
    simpa [prefixWord, tailWord_544031, baseEnd_544031] using wordTrace_append hprefix tailTrace_544031
  have hstable : (prefixWord ++ tailWord_544031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544031).length < 2 ^ (prefixWord ++ tailWord_544031).sum := by decide
  have hdescent : baseEnd_544031 < baseStart_544031 := by decide
  rcases family_descends (prefixWord ++ tailWord_544031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544076 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_544076 : Nat := 118140960795 + 544076 * 2 ^ 59
def prefixEnd_544076 : Nat := 4983230072969 + 3 ^ 40 * 544076 * 2
def baseEnd_544076 : Nat := 248331111622860918975863

theorem tailTrace_544076 : CollatzResearch.WordTrace tailWord_544076 prefixEnd_544076 248331111622860918975863 := by
  unfold tailWord_544076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9922040988456523814054041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13229387984608698418738721 9922040988456523814054041)
  ·
    refine ⟨7441530741342392860540531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9922040988456523814054041 7441530741342392860540531)
    ·
      refine ⟨11162296112013589290810797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441530741342392860540531 11162296112013589290810797)
      ·
        refine ⟨4185861042005095984054049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11162296112013589290810797 4185861042005095984054049)
        ·
          refine ⟨3139395781503821988040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4185861042005095984054049 3139395781503821988040537)
          ·
            refine ⟨2354546836127866491030403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3139395781503821988040537 2354546836127866491030403)
            ·
              refine ⟨3531820254191799736545605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354546836127866491030403 3531820254191799736545605)
              ·
                refine ⟨662216297660962450602301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3531820254191799736545605 662216297660962450602301)
                ·
                  refine ⟨248331111622860918975863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662216297660962450602301 248331111622860918975863)
                  ·
                    rfl

theorem cell20_544076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_544076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544076 prefixEnd_544076 := by exact prefixLift 544076
  have htrace : WordTrace (prefixWord ++ tailWord_544076) baseStart_544076 baseEnd_544076 := by
    simpa [prefixWord, tailWord_544076, baseEnd_544076] using wordTrace_append hprefix tailTrace_544076
  have hstable : (prefixWord ++ tailWord_544076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544076).length < 2 ^ (prefixWord ++ tailWord_544076).sum := by decide
  have hdescent : baseEnd_544076 < baseStart_544076 := by decide
  rcases family_descends (prefixWord ++ tailWord_544076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544090 : List Nat := [3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_544090 : Nat := 118140960795 + 544090 * 2 ^ 59
def prefixEnd_544090 : Nat := 4983230072969 + 3 ^ 40 * 544090 * 2
def baseEnd_544090 : Nat := 82779167201446364169713

theorem tailTrace_544090 : CollatzResearch.WordTrace tailWord_544090 prefixEnd_544090 82779167201446364169713 := by
  unfold tailWord_544090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961148149715582004779431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13229728399241552012745149 4961148149715582004779431)
  ·
    refine ⟨7441722224573373007169147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961148149715582004779431 7441722224573373007169147)
    ·
      refine ⟨11162583336860059510753721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441722224573373007169147 11162583336860059510753721)
      ·
        refine ⟨8371937502645044633065291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11162583336860059510753721 8371937502645044633065291)
        ·
          refine ⟨12557906253967566949597937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8371937502645044633065291 12557906253967566949597937)
          ·
            refine ⟨9418429690475675212198453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12557906253967566949597937 9418429690475675212198453)
            ·
              refine ⟨882977783482094551143605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9418429690475675212198453 882977783482094551143605)
              ·
                refine ⟨82779167201446364169713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 882977783482094551143605 82779167201446364169713)
                ·
                  rfl

theorem cell20_544090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_544090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544090 prefixEnd_544090 := by exact prefixLift 544090
  have htrace : WordTrace (prefixWord ++ tailWord_544090) baseStart_544090 baseEnd_544090 := by
    simpa [prefixWord, tailWord_544090, baseEnd_544090] using wordTrace_append hprefix tailTrace_544090
  have hstable : (prefixWord ++ tailWord_544090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544090).length < 2 ^ (prefixWord ++ tailWord_544090).sum := by decide
  have hdescent : baseEnd_544090 < baseStart_544090 := by decide
  rcases family_descends (prefixWord ++ tailWord_544090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544131 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_544131 : Nat := 118140960795 + 544131 * 2 ^ 59
def prefixEnd_544131 : Nat := 4983230072969 + 3 ^ 40 * 544131 * 2
def baseEnd_544131 : Nat := 248356215121525172142305

theorem tailTrace_544131 : CollatzResearch.WordTrace tailWord_544131 prefixEnd_544131 248356215121525172142305 := by
  unfold tailWord_544131
  simp only [CollatzResearch.WordTrace]
  refine ⟨19846087991713792021360247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13230725327809194680906831 19846087991713792021360247)
  ·
    refine ⟨29769131987570688032040371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19846087991713792021360247 29769131987570688032040371)
    ·
      refine ⟨44653697981356032048060557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29769131987570688032040371 44653697981356032048060557)
      ·
        refine ⟨16745136743008512018022709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44653697981356032048060557 16745136743008512018022709)
        ·
          refine ⟨1569856569657048001689629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16745136743008512018022709 1569856569657048001689629)
          ·
            refine ⟨588696213621393000633611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1569856569657048001689629 588696213621393000633611)
            ·
              refine ⟨883044320432089500950417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588696213621393000633611 883044320432089500950417)
              ·
                refine ⟨662283240324067125712813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883044320432089500950417 662283240324067125712813)
                ·
                  refine ⟨248356215121525172142305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662283240324067125712813 248356215121525172142305)
                  ·
                    rfl

theorem cell20_544131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_544131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544131 prefixEnd_544131 := by exact prefixLift 544131
  have htrace : WordTrace (prefixWord ++ tailWord_544131) baseStart_544131 baseEnd_544131 := by
    simpa [prefixWord, tailWord_544131, baseEnd_544131] using wordTrace_append hprefix tailTrace_544131
  have hstable : (prefixWord ++ tailWord_544131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544131).length < 2 ^ (prefixWord ++ tailWord_544131).sum := by decide
  have hdescent : baseEnd_544131 < baseStart_544131 := by decide
  rcases family_descends (prefixWord ++ tailWord_544131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544148 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_544148 : Nat := 118140960795 + 544148 * 2 ^ 59
def prefixEnd_544148 : Nat := 4983230072969 + 3 ^ 40 * 544148 * 2
def baseEnd_544148 : Nat := 248363974384748668575569

theorem tailTrace_544148 : CollatzResearch.WordTrace tailWord_544148 prefixEnd_544148 248363974384748668575569 := by
  unfold tailWord_544148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9923354016326101962364549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13231138688434802616486065 9923354016326101962364549)
  ·
    refine ⟨1860628878061144117943353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9923354016326101962364549 1860628878061144117943353)
    ·
      refine ⟨1395471658545858088457515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1860628878061144117943353 1395471658545858088457515)
      ·
        refine ⟨2093207487818787132686273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395471658545858088457515 2093207487818787132686273)
        ·
          refine ⟨1569905615864090349514705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093207487818787132686273 1569905615864090349514705)
          ·
            refine ⟨1177429211898067762136029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569905615864090349514705 1177429211898067762136029)
            ·
              refine ⟨441535954461775410801011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177429211898067762136029 441535954461775410801011)
              ·
                refine ⟨662303931692663116201517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441535954461775410801011 662303931692663116201517)
                ·
                  refine ⟨248363974384748668575569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662303931692663116201517 248363974384748668575569)
                  ·
                    rfl

theorem cell20_544148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_544148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544148 prefixEnd_544148 := by exact prefixLift 544148
  have htrace : WordTrace (prefixWord ++ tailWord_544148) baseStart_544148 baseEnd_544148 := by
    simpa [prefixWord, tailWord_544148, baseEnd_544148] using wordTrace_append hprefix tailTrace_544148
  have hstable : (prefixWord ++ tailWord_544148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544148).length < 2 ^ (prefixWord ++ tailWord_544148).sum := by decide
  have hdescent : baseEnd_544148 < baseStart_544148 := by decide
  rcases family_descends (prefixWord ++ tailWord_544148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544158 : List Nat := [4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_544158 : Nat := 118140960795 + 544158 * 2 ^ 59
def prefixEnd_544158 : Nat := 4983230072969 + 3 ^ 40 * 544158 * 2
def baseEnd_544158 : Nat := 82789512885744359414065

theorem tailTrace_544158 : CollatzResearch.WordTrace tailWord_544158 prefixEnd_544158 82789512885744359414065 := by
  unfold tailWord_544158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480884095326996954074141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13231381841743983755062085 2480884095326996954074141)
  ·
    refine ⟨930331535747623857777803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2480884095326996954074141 930331535747623857777803)
    ·
      refine ⟨1395497303621435786666705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930331535747623857777803 1395497303621435786666705)
      ·
        refine ⟨1046622977716076840000029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395497303621435786666705 1046622977716076840000029)
        ·
          refine ⟨392483616643528815000011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046622977716076840000029 392483616643528815000011)
          ·
            refine ⟨588725424965293222500017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392483616643528815000011 588725424965293222500017)
            ·
              refine ⟨441544068723969916875013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588725424965293222500017 441544068723969916875013)
              ·
                refine ⟨82789512885744359414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441544068723969916875013 82789512885744359414065)
                ·
                  rfl

theorem cell20_544158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_544158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544158 prefixEnd_544158 := by exact prefixLift 544158
  have htrace : WordTrace (prefixWord ++ tailWord_544158) baseStart_544158 baseEnd_544158 := by
    simpa [prefixWord, tailWord_544158, baseEnd_544158] using wordTrace_append hprefix tailTrace_544158
  have hstable : (prefixWord ++ tailWord_544158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544158).length < 2 ^ (prefixWord ++ tailWord_544158).sum := by decide
  have hdescent : baseEnd_544158 < baseStart_544158 := by decide
  rcases family_descends (prefixWord ++ tailWord_544158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544159 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_544159 : Nat := 118140960795 + 544159 * 2 ^ 59
def prefixEnd_544159 : Nat := 4983230072969 + 3 ^ 40 * 544159 * 2
def baseEnd_544159 : Nat := 248368995084481519208857

theorem tailTrace_544159 : CollatzResearch.WordTrace tailWord_544159 prefixEnd_544159 248368995084481519208857 := by
  unfold tailWord_544159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19847109235612352803379531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13231406157074901868919687 19847109235612352803379531)
  ·
    refine ⟨29770663853418529205069297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19847109235612352803379531 29770663853418529205069297)
    ·
      refine ⟨22327997890063896903801973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29770663853418529205069297 22327997890063896903801973)
      ·
        refine ⟨2093249802193490334731435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22327997890063896903801973 2093249802193490334731435)
        ·
          refine ⟨3139874703290235502097153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093249802193490334731435 3139874703290235502097153)
          ·
            refine ⟨2354906027467676626572865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3139874703290235502097153 2354906027467676626572865)
            ·
              refine ⟨1766179520600757469929649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354906027467676626572865 1766179520600757469929649)
              ·
                refine ⟨1324634640450568102447237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766179520600757469929649 1324634640450568102447237)
                ·
                  refine ⟨248368995084481519208857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324634640450568102447237 248368995084481519208857)
                  ·
                    rfl

theorem cell20_544159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_544159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544159 prefixEnd_544159 := by exact prefixLift 544159
  have htrace : WordTrace (prefixWord ++ tailWord_544159) baseStart_544159 baseEnd_544159 := by
    simpa [prefixWord, tailWord_544159, baseEnd_544159] using wordTrace_append hprefix tailTrace_544159
  have hstable : (prefixWord ++ tailWord_544159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544159).length < 2 ^ (prefixWord ++ tailWord_544159).sum := by decide
  have hdescent : baseEnd_544159 < baseStart_544159 := by decide
  rcases family_descends (prefixWord ++ tailWord_544159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544162 : List Nat := [3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_544162 : Nat := 118140960795 + 544162 * 2 ^ 59
def prefixEnd_544162 : Nat := 4983230072969 + 3 ^ 40 * 544162 * 2
def baseEnd_544162 : Nat := 82790121455408947369615

theorem tailTrace_544162 : CollatzResearch.WordTrace tailWord_544162 prefixEnd_544162 82790121455408947369615 := by
  unfold tailWord_544162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961804663650371078934685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13231479103067656210492493 4961804663650371078934685)
  ·
    refine ⟨1860676748868889154600507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4961804663650371078934685 1860676748868889154600507)
    ·
      refine ⟨2791015123303333731900761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860676748868889154600507 2791015123303333731900761)
      ·
        refine ⟨2093261342477500298925571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791015123303333731900761 2093261342477500298925571)
        ·
          refine ⟨3139892013716250448388357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093261342477500298925571 3139892013716250448388357)
          ·
            refine ⟨588729752571796959072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3139892013716250448388357 588729752571796959072817)
            ·
              refine ⟨441547314428847719304613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588729752571796959072817 441547314428847719304613)
              ·
                refine ⟨82790121455408947369615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441547314428847719304613 82790121455408947369615)
                ·
                  rfl

theorem cell20_544162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_544162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544162 prefixEnd_544162 := by exact prefixLift 544162
  have htrace : WordTrace (prefixWord ++ tailWord_544162) baseStart_544162 baseEnd_544162 := by
    simpa [prefixWord, tailWord_544162, baseEnd_544162] using wordTrace_append hprefix tailTrace_544162
  have hstable : (prefixWord ++ tailWord_544162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544162).length < 2 ^ (prefixWord ++ tailWord_544162).sum := by decide
  have hdescent : baseEnd_544162 < baseStart_544162 := by decide
  rcases family_descends (prefixWord ++ tailWord_544162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544190 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_544190 : Nat := 118140960795 + 544190 * 2 ^ 59
def prefixEnd_544190 : Nat := 4983230072969 + 3 ^ 40 * 544190 * 2
def baseEnd_544190 : Nat := 248383144329183189175397

theorem tailTrace_544190 : CollatzResearch.WordTrace tailWord_544190 prefixEnd_544190 248383144329183189175397 := by
  unfold tailWord_544190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481029987312505637219753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13232159932333363398505349 2481029987312505637219753)
  ·
    refine ⟨1860772490484379227914815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2481029987312505637219753 1860772490484379227914815)
    ·
      refine ⟨2791158735726568841872223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860772490484379227914815 2791158735726568841872223)
      ·
        refine ⟨4186738103589853262808335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791158735726568841872223 4186738103589853262808335)
        ·
          refine ⟨6280107155384779894212503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186738103589853262808335 6280107155384779894212503)
          ·
            refine ⟨9420160733077169841318755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280107155384779894212503 9420160733077169841318755)
            ·
              refine ⟨14130241099615754761978133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420160733077169841318755 14130241099615754761978133)
              ·
                refine ⟨662355051544488504467725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14130241099615754761978133 662355051544488504467725)
                ·
                  refine ⟨248383144329183189175397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662355051544488504467725 248383144329183189175397)
                  ·
                    rfl

theorem cell20_544190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_544190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544190 prefixEnd_544190 := by exact prefixLift 544190
  have htrace : WordTrace (prefixWord ++ tailWord_544190) baseStart_544190 baseEnd_544190 := by
    simpa [prefixWord, tailWord_544190, baseEnd_544190] using wordTrace_append hprefix tailTrace_544190
  have hstable : (prefixWord ++ tailWord_544190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544190).length < 2 ^ (prefixWord ++ tailWord_544190).sum := by decide
  have hdescent : baseEnd_544190 < baseStart_544190 := by decide
  rcases family_descends (prefixWord ++ tailWord_544190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544204 : List Nat := [2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_544204 : Nat := 118140960795 + 544204 * 2 ^ 59
def prefixEnd_544204 : Nat := 4983230072969 + 3 ^ 40 * 544204 * 2
def baseEnd_544204 : Nat := 82796511436887120902891

theorem tailTrace_544204 : CollatzResearch.WordTrace tailWord_544204 prefixEnd_544204 82796511436887120902891 := by
  unfold tailWord_544204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924375260224662744383833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13232500346966216992511777 9924375260224662744383833)
  ·
    refine ⟨7443281445168497058287875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9924375260224662744383833 7443281445168497058287875)
    ·
      refine ⟨11164922167752745587431813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7443281445168497058287875 11164922167752745587431813)
      ·
        refine ⟨2093422906453639797643465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11164922167752745587431813 2093422906453639797643465)
        ·
          refine ⟨1570067179840229848232599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093422906453639797643465 1570067179840229848232599)
          ·
            refine ⟨2355100769760344772348899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570067179840229848232599 2355100769760344772348899)
            ·
              refine ⟨3532651154640517158523349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355100769760344772348899 3532651154640517158523349)
              ·
                refine ⟨82796511436887120902891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3532651154640517158523349 82796511436887120902891)
                ·
                  rfl

theorem cell20_544204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_544204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544204 prefixEnd_544204 := by exact prefixLift 544204
  have htrace : WordTrace (prefixWord ++ tailWord_544204) baseStart_544204 baseEnd_544204 := by
    simpa [prefixWord, tailWord_544204, baseEnd_544204] using wordTrace_append hprefix tailTrace_544204
  have hstable : (prefixWord ++ tailWord_544204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544204).length < 2 ^ (prefixWord ++ tailWord_544204).sum := by decide
  have hdescent : baseEnd_544204 < baseStart_544204 := by decide
  rcases family_descends (prefixWord ++ tailWord_544204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544242 : List Nat := [3, 2, 1, 4, 1, 9]
def baseStart_544242 : Nat := 118140960795 + 544242 * 2 ^ 59
def prefixEnd_544242 : Nat := 4983230072969 + 3 ^ 40 * 544242 * 2
def baseEnd_544242 : Nat := 9200254760966745164513

theorem tailTrace_544242 : CollatzResearch.WordTrace tailWord_544242 prefixEnd_544242 9200254760966745164513 := by
  unfold tailWord_544242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962534123577914494662745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13233424329541105319100653 4962534123577914494662745)
  ·
    refine ⟨3721900592683435870997059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4962534123577914494662745 3721900592683435870997059)
    ·
      refine ⟨5582850889025153806495589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721900592683435870997059 5582850889025153806495589)
      ·
        refine ⟨1046784541692216338717923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5582850889025153806495589 1046784541692216338717923)
        ·
          refine ⟨1570176812538324508076885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046784541692216338717923 1570176812538324508076885)
          ·
            refine ⟨9200254760966745164513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1570176812538324508076885 9200254760966745164513)
            ·
              rfl

theorem cell20_544242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 9].length) (baseStart_544242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544242 prefixEnd_544242 := by exact prefixLift 544242
  have htrace : WordTrace (prefixWord ++ tailWord_544242) baseStart_544242 baseEnd_544242 := by
    simpa [prefixWord, tailWord_544242, baseEnd_544242] using wordTrace_append hprefix tailTrace_544242
  have hstable : (prefixWord ++ tailWord_544242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544242).length < 2 ^ (prefixWord ++ tailWord_544242).sum := by decide
  have hdescent : baseEnd_544242 < baseStart_544242 := by decide
  rcases family_descends (prefixWord ++ tailWord_544242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544245 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_544245 : Nat := 118140960795 + 544245 * 2 ^ 59
def prefixEnd_544245 : Nat := 4983230072969 + 3 ^ 40 * 544245 * 2
def baseEnd_544245 : Nat := 248408247827847442341839

theorem tailTrace_544245 : CollatzResearch.WordTrace tailWord_544245 prefixEnd_544245 248408247827847442341839 := by
  unfold tailWord_544245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19850245913300789491010189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13233497275533859660673459 19850245913300789491010189)
  ·
    refine ⟨7443842217487796059128821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19850245913300789491010189 7443842217487796059128821)
    ·
      refine ⟨697860207889480880543327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7443842217487796059128821 697860207889480880543327)
      ·
        refine ⟨1046790311834221320814991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697860207889480880543327 1046790311834221320814991)
        ·
          refine ⟨1570185467751331981222487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046790311834221320814991 1570185467751331981222487)
          ·
            refine ⟨2355278201626997971833731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570185467751331981222487 2355278201626997971833731)
            ·
              refine ⟨3532917302440496957750597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355278201626997971833731 3532917302440496957750597)
              ·
                refine ⟨662421994207593179578237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3532917302440496957750597 662421994207593179578237)
                ·
                  refine ⟨248408247827847442341839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662421994207593179578237 248408247827847442341839)
                  ·
                    rfl

theorem cell20_544245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_544245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544245 prefixEnd_544245 := by exact prefixLift 544245
  have htrace : WordTrace (prefixWord ++ tailWord_544245) baseStart_544245 baseEnd_544245 := by
    simpa [prefixWord, tailWord_544245, baseEnd_544245] using wordTrace_append hprefix tailTrace_544245
  have hstable : (prefixWord ++ tailWord_544245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544245).length < 2 ^ (prefixWord ++ tailWord_544245).sum := by decide
  have hdescent : baseEnd_544245 < baseStart_544245 := by decide
  rcases family_descends (prefixWord ++ tailWord_544245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544266 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_544266 : Nat := 118140960795 + 544266 * 2 ^ 59
def prefixEnd_544266 : Nat := 4983230072969 + 3 ^ 40 * 544266 * 2
def baseEnd_544266 : Nat := 248417832800064702641753

theorem tailTrace_544266 : CollatzResearch.WordTrace tailWord_544266 prefixEnd_544266 248417832800064702641753 := by
  unfold tailWord_544266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962752961556177519381163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13234007897483140051683101 4962752961556177519381163)
  ·
    refine ⟨7444129442334266279071745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962752961556177519381163 7444129442334266279071745)
    ·
      refine ⟨5583097081750699709303809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7444129442334266279071745 5583097081750699709303809)
      ·
        refine ⟨4187322811313024781977857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5583097081750699709303809 4187322811313024781977857)
        ·
          refine ⟨3140492108484768586483393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4187322811313024781977857 3140492108484768586483393)
          ·
            refine ⟨2355369081363576439862545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140492108484768586483393 2355369081363576439862545)
            ·
              refine ⟨1766526811022682329896909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355369081363576439862545 1766526811022682329896909)
              ·
                refine ⟨662447554133505873711341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1766526811022682329896909 662447554133505873711341)
                ·
                  refine ⟨248417832800064702641753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662447554133505873711341 248417832800064702641753)
                  ·
                    rfl

theorem cell20_544266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_544266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544266 prefixEnd_544266 := by exact prefixLift 544266
  have htrace : WordTrace (prefixWord ++ tailWord_544266) baseStart_544266 baseEnd_544266 := by
    simpa [prefixWord, tailWord_544266, baseEnd_544266] using wordTrace_append hprefix tailTrace_544266
  have hstable : (prefixWord ++ tailWord_544266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544266).length < 2 ^ (prefixWord ++ tailWord_544266).sum := by decide
  have hdescent : baseEnd_544266 < baseStart_544266 := by decide
  rcases family_descends (prefixWord ++ tailWord_544266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544290 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_544290 : Nat := 118140960795 + 544290 * 2 ^ 59
def prefixEnd_544290 : Nat := 4983230072969 + 3 ^ 40 * 544290 * 2
def baseEnd_544290 : Nat := 248428787054027285841655

theorem tailTrace_544290 : CollatzResearch.WordTrace tailWord_544290 prefixEnd_544290 248428787054027285841655 := by
  unfold tailWord_544290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962971799534440544099581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13234591465425174784265549 4962971799534440544099581)
  ·
    refine ⟨1861114424825415204037343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4962971799534440544099581 1861114424825415204037343)
    ·
      refine ⟨2791671637238122806056015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1861114424825415204037343 2791671637238122806056015)
      ·
        refine ⟨4187507455857184209084023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791671637238122806056015 4187507455857184209084023)
        ·
          refine ⟨6281261183785776313626035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187507455857184209084023 6281261183785776313626035)
          ·
            refine ⟨9421891775678664470439053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6281261183785776313626035 9421891775678664470439053)
            ·
              refine ⟨3533209415879499176414645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9421891775678664470439053 3533209415879499176414645)
              ·
                refine ⟨331238382738703047788873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3533209415879499176414645 331238382738703047788873)
                ·
                  refine ⟨248428787054027285841655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331238382738703047788873 248428787054027285841655)
                  ·
                    rfl

theorem cell20_544290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_544290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544290 prefixEnd_544290 := by exact prefixLift 544290
  have htrace : WordTrace (prefixWord ++ tailWord_544290) baseStart_544290 baseEnd_544290 := by
    simpa [prefixWord, tailWord_544290, baseEnd_544290] using wordTrace_append hprefix tailTrace_544290
  have hstable : (prefixWord ++ tailWord_544290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544290).length < 2 ^ (prefixWord ++ tailWord_544290).sum := by decide
  have hdescent : baseEnd_544290 < baseStart_544290 := by decide
  rcases family_descends (prefixWord ++ tailWord_544290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544311 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_544311 : Nat := 118140960795 + 544311 * 2 ^ 59
def prefixEnd_544311 : Nat := 4983230072969 + 3 ^ 40 * 544311 * 2
def baseEnd_544311 : Nat := 248438372026244546141569

theorem tailTrace_544311 : CollatzResearch.WordTrace tailWord_544311 prefixEnd_544311 248438372026244546141569 := by
  unfold tailWord_544311
  simp only [CollatzResearch.WordTrace]
  refine ⟨19852653131061682762912787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13235102087374455175275191 19852653131061682762912787)
  ·
    refine ⟨29778979696592524144369181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19852653131061682762912787 29778979696592524144369181)
    ·
      refine ⟨11167117386222196554138443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29778979696592524144369181 11167117386222196554138443)
      ·
        refine ⟨16750676079333294831207665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11167117386222196554138443 16750676079333294831207665)
        ·
          refine ⟨12563007059499971123405749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16750676079333294831207665 12563007059499971123405749)
          ·
            refine ⟨1177781911828122292819289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12563007059499971123405749 1177781911828122292819289)
            ·
              refine ⟨883336433871091719614467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177781911828122292819289 883336433871091719614467)
              ·
                refine ⟨1325004650806637579421701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883336433871091719614467 1325004650806637579421701)
                ·
                  refine ⟨248438372026244546141569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1325004650806637579421701 248438372026244546141569)
                  ·
                    rfl

theorem cell20_544311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_544311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544311 prefixEnd_544311 := by exact prefixLift 544311
  have htrace : WordTrace (prefixWord ++ tailWord_544311) baseStart_544311 baseEnd_544311 := by
    simpa [prefixWord, tailWord_544311, baseEnd_544311] using wordTrace_append hprefix tailTrace_544311
  have hstable : (prefixWord ++ tailWord_544311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544311).length < 2 ^ (prefixWord ++ tailWord_544311).sum := by decide
  have hdescent : baseEnd_544311 < baseStart_544311 := by decide
  rcases family_descends (prefixWord ++ tailWord_544311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544321 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_544321 : Nat := 118140960795 + 544321 * 2 ^ 59
def prefixEnd_544321 : Nat := 4983230072969 + 3 ^ 40 * 544321 * 2
def baseEnd_544321 : Nat := 248442936298728955808195

theorem tailTrace_544321 : CollatzResearch.WordTrace tailWord_544321 prefixEnd_544321 248442936298728955808195 := by
  unfold tailWord_544321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19853017861025454470776817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13235345240683636313851211 19853017861025454470776817)
  ·
    refine ⟨14889763395769090853082613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19853017861025454470776817 14889763395769090853082613)
    ·
      refine ⟨1395915318353352267476495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14889763395769090853082613 1395915318353352267476495)
      ·
        refine ⟨2093872977530028401214743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395915318353352267476495 2093872977530028401214743)
        ·
          refine ⟨3140809466295042601822115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093872977530028401214743 3140809466295042601822115)
          ·
            refine ⟨4711214199442563902733173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140809466295042601822115 4711214199442563902733173)
            ·
              refine ⟨441676331197740365881235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4711214199442563902733173 441676331197740365881235)
              ·
                refine ⟨662514496796610548821853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441676331197740365881235 662514496796610548821853)
                ·
                  refine ⟨248442936298728955808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662514496796610548821853 248442936298728955808195)
                  ·
                    rfl

theorem cell20_544321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_544321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544321 prefixEnd_544321 := by exact prefixLift 544321
  have htrace : WordTrace (prefixWord ++ tailWord_544321) baseStart_544321 baseEnd_544321 := by
    simpa [prefixWord, tailWord_544321, baseEnd_544321] using wordTrace_append hprefix tailTrace_544321
  have hstable : (prefixWord ++ tailWord_544321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544321).length < 2 ^ (prefixWord ++ tailWord_544321).sum := by decide
  have hdescent : baseEnd_544321 < baseStart_544321 := by decide
  rcases family_descends (prefixWord ++ tailWord_544321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544356 : List Nat := [2, 3, 1, 1, 2, 5, 6]
def baseStart_544356 : Nat := 118140960795 + 544356 * 2 ^ 59
def prefixEnd_544356 : Nat := 4983230072969 + 3 ^ 40 * 544356 * 2
def baseEnd_544356 : Nat := 27606545694713821071265

theorem tailTrace_544356 : CollatzResearch.WordTrace tailWord_544356 prefixEnd_544356 27606545694713821071265 := by
  unfold tailWord_544356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927147207949327724150461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13236196277265770298867281 9927147207949327724150461)
  ·
    refine ⟨3722680202980997896556423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9927147207949327724150461 3722680202980997896556423)
    ·
      refine ⟨5584020304471496844834635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722680202980997896556423 5584020304471496844834635)
      ·
        refine ⟨8376030456707245267251953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5584020304471496844834635 8376030456707245267251953)
        ·
          refine ⟨6282022842530433950438965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8376030456707245267251953 6282022842530433950438965)
          ·
            refine ⟨588939641487228182853653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6282022842530433950438965 588939641487228182853653)
            ·
              refine ⟨27606545694713821071265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 588939641487228182853653 27606545694713821071265)
              ·
                rfl

theorem cell20_544356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_544356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544356 prefixEnd_544356 := by exact prefixLift 544356
  have htrace : WordTrace (prefixWord ++ tailWord_544356) baseStart_544356 baseEnd_544356 := by
    simpa [prefixWord, tailWord_544356, baseEnd_544356] using wordTrace_append hprefix tailTrace_544356
  have hstable : (prefixWord ++ tailWord_544356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544356).length < 2 ^ (prefixWord ++ tailWord_544356).sum := by decide
  have hdescent : baseEnd_544356 < baseStart_544356 := by decide
  rcases family_descends (prefixWord ++ tailWord_544356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544373 : List Nat := [1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_544373 : Nat := 118140960795 + 544373 * 2 ^ 59
def prefixEnd_544373 : Nat := 4983230072969 + 3 ^ 40 * 544373 * 2
def baseEnd_544373 : Nat := 82822223505215962024883

theorem tailTrace_544373 : CollatzResearch.WordTrace tailWord_544373 prefixEnd_544373 82822223505215962024883 := by
  unfold tailWord_544373
  simp only [CollatzResearch.WordTrace]
  refine ⟨19854914456837067351669773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13236609637891378234446515 19854914456837067351669773)
  ·
    refine ⟨7445592921313900256876165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19854914456837067351669773 7445592921313900256876165)
    ·
      refine ⟨1396048672746356298164281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7445592921313900256876165 1396048672746356298164281)
      ·
        refine ⟨1047036504559767223623211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1396048672746356298164281 1047036504559767223623211)
        ·
          refine ⟨1570554756839650835434817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047036504559767223623211 1570554756839650835434817)
          ·
            refine ⟨1177916067629738126576113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1570554756839650835434817 1177916067629738126576113)
            ·
              refine ⟨883437050722303594932085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177916067629738126576113 883437050722303594932085)
              ·
                refine ⟨82822223505215962024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883437050722303594932085 82822223505215962024883)
                ·
                  rfl

theorem cell20_544373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_544373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544373 prefixEnd_544373 := by exact prefixLift 544373
  have htrace : WordTrace (prefixWord ++ tailWord_544373) baseStart_544373 baseEnd_544373 := by
    simpa [prefixWord, tailWord_544373, baseEnd_544373] using wordTrace_append hprefix tailTrace_544373
  have hstable : (prefixWord ++ tailWord_544373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544373).length < 2 ^ (prefixWord ++ tailWord_544373).sum := by decide
  have hdescent : baseEnd_544373 < baseStart_544373 := by decide
  rcases family_descends (prefixWord ++ tailWord_544373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544394 : List Nat := [3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_544394 : Nat := 118140960795 + 544394 * 2 ^ 59
def prefixEnd_544394 : Nat := 4983230072969 + 3 ^ 40 * 544394 * 2
def baseEnd_544394 : Nat := 82825418495955048791521

theorem tailTrace_544394 : CollatzResearch.WordTrace tailWord_544394 prefixEnd_544394 82825418495955048791521 := by
  unfold tailWord_544394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963920097440246984546059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13237120259840658625456157 4963920097440246984546059)
  ·
    refine ⟨7445880146160370476819089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4963920097440246984546059 7445880146160370476819089)
    ·
      refine ⟨5584410109620277857614317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7445880146160370476819089 5584410109620277857614317)
      ·
        refine ⟨2094153791107604196605369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5584410109620277857614317 2094153791107604196605369)
        ·
          refine ⟨1570615343330703147454027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094153791107604196605369 1570615343330703147454027)
          ·
            refine ⟨2355923014996054721181041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570615343330703147454027 2355923014996054721181041)
            ·
              refine ⟨1766942261247041040885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355923014996054721181041 1766942261247041040885781)
              ·
                refine ⟨82825418495955048791521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1766942261247041040885781 82825418495955048791521)
                ·
                  rfl

theorem cell20_544394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_544394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544394 prefixEnd_544394 := by exact prefixLift 544394
  have htrace : WordTrace (prefixWord ++ tailWord_544394) baseStart_544394 baseEnd_544394 := by
    simpa [prefixWord, tailWord_544394, baseEnd_544394] using wordTrace_append hprefix tailTrace_544394
  have hstable : (prefixWord ++ tailWord_544394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544394).length < 2 ^ (prefixWord ++ tailWord_544394).sum := by decide
  have hdescent : baseEnd_544394 < baseStart_544394 := by decide
  rcases family_descends (prefixWord ++ tailWord_544394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544424 : List Nat := [2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_544424 : Nat := 118140960795 + 544424 * 2 ^ 59
def prefixEnd_544424 : Nat := 4983230072969 + 3 ^ 40 * 544424 * 2
def baseEnd_544424 : Nat := 82829982768439458458147

theorem tailTrace_544424 : CollatzResearch.WordTrace tailWord_544424 prefixEnd_544424 82829982768439458458147 := by
  unfold tailWord_544424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928387289826151530888163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13237849719768202041184217 9928387289826151530888163)
  ·
    refine ⟨14892580934739227296332245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9928387289826151530888163 14892580934739227296332245)
    ·
      refine ⟨349044865657950639757787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14892580934739227296332245 349044865657950639757787)
      ·
        refine ⟨523567298486925959636681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349044865657950639757787 523567298486925959636681)
        ·
          refine ⟨392675473865194469727511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523567298486925959636681 392675473865194469727511)
          ·
            refine ⟨589013210797791704591267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392675473865194469727511 589013210797791704591267)
            ·
              refine ⟨883519816196687556886901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589013210797791704591267 883519816196687556886901)
              ·
                refine ⟨82829982768439458458147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883519816196687556886901 82829982768439458458147)
                ·
                  rfl

theorem cell20_544424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_544424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544424 prefixEnd_544424 := by exact prefixLift 544424
  have htrace : WordTrace (prefixWord ++ tailWord_544424) baseStart_544424 baseEnd_544424 := by
    simpa [prefixWord, tailWord_544424, baseEnd_544424] using wordTrace_append hprefix tailTrace_544424
  have hstable : (prefixWord ++ tailWord_544424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544424).length < 2 ^ (prefixWord ++ tailWord_544424).sum := by decide
  have hdescent : baseEnd_544424 < baseStart_544424 := by decide
  rcases family_descends (prefixWord ++ tailWord_544424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544535 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 2]
def baseStart_544535 : Nat := 118140960795 + 544535 * 2 ^ 59
def prefixEnd_544535 : Nat := 4983230072969 + 3 ^ 40 * 544535 * 2
def baseEnd_544535 : Nat := 248540611729895322673987

theorem tailTrace_544535 : CollatzResearch.WordTrace tailWord_544535 prefixEnd_544535 248540611729895322673987 := by
  unfold tailWord_544535
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860823082250169019067059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13240548721500112679378039 19860823082250169019067059)
  ·
    refine ⟨29791234623375253528600589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860823082250169019067059 29791234623375253528600589)
    ·
      refine ⟨11171712983765720073225221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29791234623375253528600589 11171712983765720073225221)
      ·
        refine ⟨2094696184456072513729729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11171712983765720073225221 2094696184456072513729729)
        ·
          refine ⟨1571022138342054385297297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094696184456072513729729 1571022138342054385297297)
          ·
            refine ⟨1178266603756540788972973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571022138342054385297297 1178266603756540788972973)
            ·
              refine ⟨441849976408702795864865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1178266603756540788972973 441849976408702795864865)
              ·
                refine ⟨331387482306527096898649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441849976408702795864865 331387482306527096898649)
                ·
                  refine ⟨248540611729895322673987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331387482306527096898649 248540611729895322673987)
                  ·
                    rfl

theorem cell20_544535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2].length) (baseStart_544535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544535 prefixEnd_544535 := by exact prefixLift 544535
  have htrace : WordTrace (prefixWord ++ tailWord_544535) baseStart_544535 baseEnd_544535 := by
    simpa [prefixWord, tailWord_544535, baseEnd_544535] using wordTrace_append hprefix tailTrace_544535
  have hstable : (prefixWord ++ tailWord_544535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544535).length < 2 ^ (prefixWord ++ tailWord_544535).sum := by decide
  have hdescent : baseEnd_544535 < baseStart_544535 := by decide
  rcases family_descends (prefixWord ++ tailWord_544535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544546 : List Nat := [3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_544546 : Nat := 118140960795 + 544546 * 2 ^ 59
def prefixEnd_544546 : Nat := 4983230072969 + 3 ^ 40 * 544546 * 2
def baseEnd_544546 : Nat := 82848544143209391102425

theorem tailTrace_544546 : CollatzResearch.WordTrace tailWord_544546 prefixEnd_544546 82848544143209391102425 := by
  unfold tailWord_544546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965306071302579474429373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13240816190140211931811661 4965306071302579474429373)
  ·
    refine ⟨1861989776738467302911015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4965306071302579474429373 1861989776738467302911015)
    ·
      refine ⟨2792984665107700954366523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1861989776738467302911015 2792984665107700954366523)
      ·
        refine ⟨4189476997661551431549785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792984665107700954366523 4189476997661551431549785)
        ·
          refine ⟨3142107748246163573662339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189476997661551431549785 3142107748246163573662339)
          ·
            refine ⟨4713161622369245360493509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142107748246163573662339 4713161622369245360493509)
            ·
              refine ⟨883717804194233505092533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4713161622369245360493509 883717804194233505092533)
              ·
                refine ⟨82848544143209391102425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883717804194233505092533 82848544143209391102425)
                ·
                  rfl

theorem cell20_544546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_544546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544546 prefixEnd_544546 := by exact prefixLift 544546
  have htrace : WordTrace (prefixWord ++ tailWord_544546) baseStart_544546 baseEnd_544546 := by
    simpa [prefixWord, tailWord_544546, baseEnd_544546] using wordTrace_append hprefix tailTrace_544546
  have hstable : (prefixWord ++ tailWord_544546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544546).length < 2 ^ (prefixWord ++ tailWord_544546).sum := by decide
  have hdescent : baseEnd_544546 < baseStart_544546 := by decide
  rcases family_descends (prefixWord ++ tailWord_544546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544549 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_544549 : Nat := 118140960795 + 544549 * 2 ^ 59
def prefixEnd_544549 : Nat := 4983230072969 + 3 ^ 40 * 544549 * 2
def baseEnd_544549 : Nat := 248547001711373496207263

theorem tailTrace_544549 : CollatzResearch.WordTrace tailWord_544549 prefixEnd_544549 248547001711373496207263 := by
  unfold tailWord_544549
  simp only [CollatzResearch.WordTrace]
  refine ⟨19861333704199449410076701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13240889136132966273384467 19861333704199449410076701)
  ·
    refine ⟨7448000139074793528778763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19861333704199449410076701 7448000139074793528778763)
    ·
      refine ⟨11172000208612190293168145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7448000139074793528778763 11172000208612190293168145)
      ·
        refine ⟨8379000156459142719876109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11172000208612190293168145 8379000156459142719876109)
        ·
          refine ⟨3142125058672178519953541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8379000156459142719876109 3142125058672178519953541)
          ·
            refine ⟨589148448501033472491289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3142125058672178519953541 589148448501033472491289)
            ·
              refine ⟨441861336375775104368467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589148448501033472491289 441861336375775104368467)
              ·
                refine ⟨662792004563662656552701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441861336375775104368467 662792004563662656552701)
                ·
                  refine ⟨248547001711373496207263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662792004563662656552701 248547001711373496207263)
                  ·
                    rfl

theorem cell20_544549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_544549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544549 prefixEnd_544549 := by exact prefixLift 544549
  have htrace : WordTrace (prefixWord ++ tailWord_544549) baseStart_544549 baseEnd_544549 := by
    simpa [prefixWord, tailWord_544549, baseEnd_544549] using wordTrace_append hprefix tailTrace_544549
  have hstable : (prefixWord ++ tailWord_544549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544549).length < 2 ^ (prefixWord ++ tailWord_544549).sum := by decide
  have hdescent : baseEnd_544549 < baseStart_544549 := by decide
  rcases family_descends (prefixWord ++ tailWord_544549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544594 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_544594 : Nat := 118140960795 + 544594 * 2 ^ 59
def prefixEnd_544594 : Nat := 4983230072969 + 3 ^ 40 * 544594 * 2
def baseEnd_544594 : Nat := 248567540937553339707079

theorem tailTrace_544594 : CollatzResearch.WordTrace tailWord_544594 prefixEnd_544594 248567540937553339707079 := by
  unfold tailWord_544594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965743747259105523866209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13241983326024281396976557 4965743747259105523866209)
  ·
    refine ⟨3724307810444329142899657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4965743747259105523866209 3724307810444329142899657)
    ·
      refine ⟨2793230857833246857174743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724307810444329142899657 2793230857833246857174743)
      ·
        refine ⟨4189846286749870285762115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793230857833246857174743 4189846286749870285762115)
        ·
          refine ⟨6284769430124805428643173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189846286749870285762115 6284769430124805428643173)
          ·
            refine ⟨1178394268148401017870595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6284769430124805428643173 1178394268148401017870595)
            ·
              refine ⟨1767591402222601526805893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178394268148401017870595 1767591402222601526805893)
              ·
                refine ⟨331423387916737786276105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1767591402222601526805893 331423387916737786276105)
                ·
                  refine ⟨248567540937553339707079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331423387916737786276105 248567540937553339707079)
                  ·
                    rfl

theorem cell20_544594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_544594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544594 prefixEnd_544594 := by exact prefixLift 544594
  have htrace : WordTrace (prefixWord ++ tailWord_544594) baseStart_544594 baseEnd_544594 := by
    simpa [prefixWord, tailWord_544594, baseEnd_544594] using wordTrace_append hprefix tailTrace_544594
  have hstable : (prefixWord ++ tailWord_544594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544594).length < 2 ^ (prefixWord ++ tailWord_544594).sum := by decide
  have hdescent : baseEnd_544594 < baseStart_544594 := by decide
  rcases family_descends (prefixWord ++ tailWord_544594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544618 : List Nat := [3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_544618 : Nat := 118140960795 + 544618 * 2 ^ 59
def prefixEnd_544618 : Nat := 4983230072969 + 3 ^ 40 * 544618 * 2
def baseEnd_544618 : Nat := 82859498397171974302327

theorem tailTrace_544618 : CollatzResearch.WordTrace tailWord_544618 prefixEnd_544618 82859498397171974302327 := by
  unfold tailWord_544618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965962585237368548584627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13242566893966316129559005 4965962585237368548584627)
  ·
    refine ⟨7448943877856052822876941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965962585237368548584627 7448943877856052822876941)
    ·
      refine ⟨2793353954196019808578853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7448943877856052822876941 2793353954196019808578853)
      ·
        refine ⟨523753866411753714108535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2793353954196019808578853 523753866411753714108535)
        ·
          refine ⟨785630799617630571162803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523753866411753714108535 785630799617630571162803)
          ·
            refine ⟨1178446199426445856744205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785630799617630571162803 1178446199426445856744205)
            ·
              refine ⟨441917324784917196279077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1178446199426445856744205 441917324784917196279077)
              ·
                refine ⟨82859498397171974302327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441917324784917196279077 82859498397171974302327)
                ·
                  rfl

theorem cell20_544618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_544618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544618 prefixEnd_544618 := by exact prefixLift 544618
  have htrace : WordTrace (prefixWord ++ tailWord_544618) baseStart_544618 baseEnd_544618 := by
    simpa [prefixWord, tailWord_544618, baseEnd_544618] using wordTrace_append hprefix tailTrace_544618
  have hstable : (prefixWord ++ tailWord_544618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544618).length < 2 ^ (prefixWord ++ tailWord_544618).sum := by decide
  have hdescent : baseEnd_544618 < baseStart_544618 := by decide
  rcases family_descends (prefixWord ++ tailWord_544618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544629 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_544629 : Nat := 118140960795 + 544629 * 2 ^ 59
def prefixEnd_544629 : Nat := 4983230072969 + 3 ^ 40 * 544629 * 2
def baseEnd_544629 : Nat := 248583515891248773540269

theorem tailTrace_544629 : CollatzResearch.WordTrace tailWord_544629 prefixEnd_544629 248583515891248773540269 := by
  unfold tailWord_544629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864251543909623072988941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13242834362606415381992627 19864251543909623072988941)
  ·
    refine ⟨7449094328966108652370853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19864251543909623072988941 7449094328966108652370853)
    ·
      refine ⟨1396705186681145372319535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7449094328966108652370853 1396705186681145372319535)
      ·
        refine ⟨2095057780021718058479303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396705186681145372319535 2095057780021718058479303)
        ·
          refine ⟨3142586670032577087718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095057780021718058479303 3142586670032577087718955)
          ·
            refine ⟨4713880005048865631578433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142586670032577087718955 4713880005048865631578433)
            ·
              refine ⟨3535410003786649223683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4713880005048865631578433 3535410003786649223683825)
              ·
                refine ⟨2651557502839986917762869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535410003786649223683825 2651557502839986917762869)
                ·
                  refine ⟨248583515891248773540269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651557502839986917762869 248583515891248773540269)
                  ·
                    rfl

theorem cell20_544629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_544629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544629 prefixEnd_544629 := by exact prefixLift 544629
  have htrace : WordTrace (prefixWord ++ tailWord_544629) baseStart_544629 baseEnd_544629 := by
    simpa [prefixWord, tailWord_544629, baseEnd_544629] using wordTrace_append hprefix tailTrace_544629
  have hstable : (prefixWord ++ tailWord_544629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544629).length < 2 ^ (prefixWord ++ tailWord_544629).sum := by decide
  have hdescent : baseEnd_544629 < baseStart_544629 := by decide
  rcases family_descends (prefixWord ++ tailWord_544629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544643 : List Nat := [1, 1, 1, 3, 4, 3, 7]
def baseStart_544643 : Nat := 118140960795 + 544643 * 2 ^ 59
def prefixEnd_544643 : Nat := 4983230072969 + 3 ^ 40 * 544643 * 2
def baseEnd_544643 : Nat := 27621100652525216341505

theorem tailTrace_544643 : CollatzResearch.WordTrace tailWord_544643 prefixEnd_544643 27621100652525216341505 := by
  unfold tailWord_544643
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864762165858903463998583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13243174777239268975999055 19864762165858903463998583)
  ·
    refine ⟨29797143248788355195997875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19864762165858903463998583 29797143248788355195997875)
    ·
      refine ⟨44695714873182532793996813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29797143248788355195997875 44695714873182532793996813)
      ·
        refine ⟨16760893077443449797748805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44695714873182532793996813 16760893077443449797748805)
        ·
          refine ⟨3142667452020646837077901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16760893077443449797748805 3142667452020646837077901)
          ·
            refine ⟨1178500294507742563904213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3142667452020646837077901 1178500294507742563904213)
            ·
              refine ⟨27621100652525216341505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1178500294507742563904213 27621100652525216341505)
              ·
                rfl

theorem cell20_544643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_544643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544643 prefixEnd_544643 := by exact prefixLift 544643
  have htrace : WordTrace (prefixWord ++ tailWord_544643) baseStart_544643 baseEnd_544643 := by
    simpa [prefixWord, tailWord_544643, baseEnd_544643] using wordTrace_append hprefix tailTrace_544643
  have hstable : (prefixWord ++ tailWord_544643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544643).length < 2 ^ (prefixWord ++ tailWord_544643).sum := by decide
  have hdescent : baseEnd_544643 < baseStart_544643 := by decide
  rcases family_descends (prefixWord ++ tailWord_544643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544719 : List Nat := [1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_544719 : Nat := 118140960795 + 544719 * 2 ^ 59
def prefixEnd_544719 : Nat := 4983230072969 + 3 ^ 40 * 544719 * 2
def baseEnd_544719 : Nat := 82874864781202820179967

theorem tailTrace_544719 : CollatzResearch.WordTrace tailWord_544719 prefixEnd_544719 82874864781202820179967 := by
  unfold tailWord_544719
  simp only [CollatzResearch.WordTrace]
  refine ⟨19867534113583568443765211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13245022742389045629176807 19867534113583568443765211)
  ·
    refine ⟨29801301170375352665647817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19867534113583568443765211 29801301170375352665647817)
    ·
      refine ⟨22350975877781514499235863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29801301170375352665647817 22350975877781514499235863)
      ·
        refine ⟨33526463816672271748853795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22350975877781514499235863 33526463816672271748853795)
        ·
          refine ⟨50289695725008407623280693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33526463816672271748853795 50289695725008407623280693)
          ·
            refine ⟨4714658974219538214682565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50289695725008407623280693 4714658974219538214682565)
            ·
              refine ⟨883998557666163415252981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4714658974219538214682565 883998557666163415252981)
              ·
                refine ⟨82874864781202820179967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883998557666163415252981 82874864781202820179967)
                ·
                  rfl

theorem cell20_544719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_544719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544719 prefixEnd_544719 := by exact prefixLift 544719
  have htrace : WordTrace (prefixWord ++ tailWord_544719) baseStart_544719 baseEnd_544719 := by
    simpa [prefixWord, tailWord_544719, baseEnd_544719] using wordTrace_append hprefix tailTrace_544719
  have hstable : (prefixWord ++ tailWord_544719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544719).length < 2 ^ (prefixWord ++ tailWord_544719).sum := by decide
  have hdescent : baseEnd_544719 < baseStart_544719 := by decide
  rcases family_descends (prefixWord ++ tailWord_544719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544757 : List Nat := [1, 3, 5, 11]
def baseStart_544757 : Nat := 118140960795 + 544757 * 2 ^ 59
def prefixEnd_544757 : Nat := 4983230072969 + 3 ^ 40 * 544757 * 2
def baseEnd_544757 : Nat := 1023217854234770441453

theorem tailTrace_544757 : CollatzResearch.WordTrace tailWord_544757 prefixEnd_544757 1023217854234770441453 := by
  unfold tailWord_544757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868920087445900933648525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13245946724963933955765683 19868920087445900933648525)
  ·
    refine ⟨7450845032792212850118197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19868920087445900933648525 7450845032792212850118197)
    ·
      refine ⟨698516721824269954698581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7450845032792212850118197 698516721824269954698581)
      ·
        refine ⟨1023217854234770441453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 698516721824269954698581 1023217854234770441453)
        ·
          rfl

theorem cell20_544757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 11].length) (baseStart_544757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544757 prefixEnd_544757 := by exact prefixLift 544757
  have htrace : WordTrace (prefixWord ++ tailWord_544757) baseStart_544757 baseEnd_544757 := by
    simpa [prefixWord, tailWord_544757, baseEnd_544757] using wordTrace_append hprefix tailTrace_544757
  have hstable : (prefixWord ++ tailWord_544757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544757).length < 2 ^ (prefixWord ++ tailWord_544757).sum := by decide
  have hdescent : baseEnd_544757 < baseStart_544757 := by decide
  rcases family_descends (prefixWord ++ tailWord_544757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544771 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_544771 : Nat := 118140960795 + 544771 * 2 ^ 59
def prefixEnd_544771 : Nat := 4983230072969 + 3 ^ 40 * 544771 * 2
def baseEnd_544771 : Nat := 248648328560527390806355

theorem tailTrace_544771 : CollatzResearch.WordTrace tailWord_544771 prefixEnd_544771 248648328560527390806355 := by
  unfold tailWord_544771
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869430709395181324658167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246287139596787549772111 19869430709395181324658167)
  ·
    refine ⟨29804146064092771986987251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19869430709395181324658167 29804146064092771986987251)
    ·
      refine ⟨44706219096139157980480877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29804146064092771986987251 44706219096139157980480877)
      ·
        refine ⟨16764832161052184242680329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44706219096139157980480877 16764832161052184242680329)
        ·
          refine ⟨12573624120789138182010247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16764832161052184242680329 12573624120789138182010247)
          ·
            refine ⟨18860436181183707273015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12573624120789138182010247 18860436181183707273015371)
            ·
              refine ⟨28290654271775560909523057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18860436181183707273015371 28290654271775560909523057)
              ·
                refine ⟨21217990703831670682142293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28290654271775560909523057 21217990703831670682142293)
                ·
                  refine ⟨248648328560527390806355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21217990703831670682142293 248648328560527390806355)
                  ·
                    rfl

theorem cell20_544771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_544771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544771 prefixEnd_544771 := by exact prefixLift 544771
  have htrace : WordTrace (prefixWord ++ tailWord_544771) baseStart_544771 baseEnd_544771 := by
    simpa [prefixWord, tailWord_544771, baseEnd_544771] using wordTrace_append hprefix tailTrace_544771
  have hstable : (prefixWord ++ tailWord_544771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544771).length < 2 ^ (prefixWord ++ tailWord_544771).sum := by decide
  have hdescent : baseEnd_544771 < baseStart_544771 := by decide
  rcases family_descends (prefixWord ++ tailWord_544771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544791 : List Nat := [1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_544791 : Nat := 118140960795 + 544791 * 2 ^ 59
def prefixEnd_544791 : Nat := 4983230072969 + 3 ^ 40 * 544791 * 2
def baseEnd_544791 : Nat := 82885819035165403379869

theorem tailTrace_544791 : CollatzResearch.WordTrace tailWord_544791 prefixEnd_544791 82885819035165403379869 := by
  unfold tailWord_544791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870160169322724740386227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246773446215149826924151 19870160169322724740386227)
  ·
    refine ⟨29805240253984087110579341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870160169322724740386227 29805240253984087110579341)
    ·
      refine ⟨11176965095244032666467253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29805240253984087110579341 11176965095244032666467253)
      ·
        refine ⟨1047840477679128062481305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11176965095244032666467253 1047840477679128062481305)
        ·
          refine ⟨785880358259346046860979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1047840477679128062481305 785880358259346046860979)
          ·
            refine ⟨1178820537389019070291469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785880358259346046860979 1178820537389019070291469)
            ·
              refine ⟨442057701520882151359301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1178820537389019070291469 442057701520882151359301)
              ·
                refine ⟨82885819035165403379869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442057701520882151359301 82885819035165403379869)
                ·
                  rfl

theorem cell20_544791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_544791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544791 prefixEnd_544791 := by exact prefixLift 544791
  have htrace : WordTrace (prefixWord ++ tailWord_544791) baseStart_544791 baseEnd_544791 := by
    simpa [prefixWord, tailWord_544791, baseEnd_544791] using wordTrace_append hprefix tailTrace_544791
  have hstable : (prefixWord ++ tailWord_544791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544791).length < 2 ^ (prefixWord ++ tailWord_544791).sum := by decide
  have hdescent : baseEnd_544791 < baseStart_544791 := by decide
  rcases family_descends (prefixWord ++ tailWord_544791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544805 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 2]
def baseStart_544805 : Nat := 118140960795 + 544805 * 2 ^ 59
def prefixEnd_544805 : Nat := 4983230072969 + 3 ^ 40 * 544805 * 2
def baseEnd_544805 : Nat := 248663847086974383672883

theorem tailTrace_544805 : CollatzResearch.WordTrace tailWord_544805 prefixEnd_544805 248663847086974383672883 := by
  unfold tailWord_544805
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870670791272005131395869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13247113860848003420930579 19870670791272005131395869)
  ·
    refine ⟨7451501546727001924273451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19870670791272005131395869 7451501546727001924273451)
    ·
      refine ⟨11177252320090502886410177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451501546727001924273451 11177252320090502886410177)
      ·
        refine ⟨8382939240067877164807633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11177252320090502886410177 8382939240067877164807633)
        ·
          refine ⟨6287204430050907873605725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8382939240067877164807633 6287204430050907873605725)
          ·
            refine ⟨2357701661269090452602147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6287204430050907873605725 2357701661269090452602147)
            ·
              refine ⟨3536552491903635678903221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357701661269090452602147 3536552491903635678903221)
              ·
                refine ⟨331551796115965844897177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3536552491903635678903221 331551796115965844897177)
                ·
                  refine ⟨248663847086974383672883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331551796115965844897177 248663847086974383672883)
                  ·
                    rfl

theorem cell20_544805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_544805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544805 prefixEnd_544805 := by exact prefixLift 544805
  have htrace : WordTrace (prefixWord ++ tailWord_544805) baseStart_544805 baseEnd_544805 := by
    simpa [prefixWord, tailWord_544805, baseEnd_544805] using wordTrace_append hprefix tailTrace_544805
  have hstable : (prefixWord ++ tailWord_544805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544805).length < 2 ^ (prefixWord ++ tailWord_544805).sum := by decide
  have hdescent : baseEnd_544805 < baseStart_544805 := by decide
  rcases family_descends (prefixWord ++ tailWord_544805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544819 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_544819 : Nat := 118140960795 + 544819 * 2 ^ 59
def prefixEnd_544819 : Nat := 4983230072969 + 3 ^ 40 * 544819 * 2
def baseEnd_544819 : Nat := 248670237068452557206159

theorem tailTrace_544819 : CollatzResearch.WordTrace tailWord_544819 prefixEnd_544819 248670237068452557206159 := by
  unfold tailWord_544819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19871181413221285522405511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13247454275480857014937007 19871181413221285522405511)
  ·
    refine ⟨29806772119831928283608267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19871181413221285522405511 29806772119831928283608267)
    ·
      refine ⟨44710158179747892425412401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29806772119831928283608267 44710158179747892425412401)
      ·
        refine ⟨33532618634810919319059301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44710158179747892425412401 33532618634810919319059301)
        ·
          refine ⟨6287365994027047372323619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33532618634810919319059301 6287365994027047372323619)
          ·
            refine ⟨9431048991040571058485429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287365994027047372323619 9431048991040571058485429)
            ·
              refine ⟨884160842910053536733009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9431048991040571058485429 884160842910053536733009)
              ·
                refine ⟨663120632182540152549757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884160842910053536733009 663120632182540152549757)
                ·
                  refine ⟨248670237068452557206159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663120632182540152549757 248670237068452557206159)
                  ·
                    rfl

theorem cell20_544819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_544819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544819 prefixEnd_544819 := by exact prefixLift 544819
  have htrace : WordTrace (prefixWord ++ tailWord_544819) baseStart_544819 baseEnd_544819 := by
    simpa [prefixWord, tailWord_544819, baseEnd_544819] using wordTrace_append hprefix tailTrace_544819
  have hstable : (prefixWord ++ tailWord_544819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544819).length < 2 ^ (prefixWord ++ tailWord_544819).sum := by decide
  have hdescent : baseEnd_544819 < baseStart_544819 := by decide
  rcases family_descends (prefixWord ++ tailWord_544819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544822 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_544822 : Nat := 118140960795 + 544822 * 2 ^ 59
def prefixEnd_544822 : Nat := 4983230072969 + 3 ^ 40 * 544822 * 2
def baseEnd_544822 : Nat := 248671606350197880106147

theorem tailTrace_544822 : CollatzResearch.WordTrace tailWord_544822 prefixEnd_544822 248671606350197880106147 := by
  unfold tailWord_544822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241955677013151064672795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13247527221473611356509813 1241955677013151064672795)
  ·
    refine ⟨1862933515519726597009193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241955677013151064672795 1862933515519726597009193)
    ·
      refine ⟨1397200136639794947756895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862933515519726597009193 1397200136639794947756895)
      ·
        refine ⟨2095800204959692421635343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397200136639794947756895 2095800204959692421635343)
        ·
          refine ⟨3143700307439538632453015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095800204959692421635343 3143700307439538632453015)
          ·
            refine ⟨4715550461159307948679523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143700307439538632453015 4715550461159307948679523)
            ·
              refine ⟨7073325691738961923019285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715550461159307948679523 7073325691738961923019285)
              ·
                refine ⟨331562141800263840141529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7073325691738961923019285 331562141800263840141529)
                ·
                  refine ⟨248671606350197880106147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331562141800263840141529 248671606350197880106147)
                  ·
                    rfl

theorem cell20_544822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_544822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544822 prefixEnd_544822 := by exact prefixLift 544822
  have htrace : WordTrace (prefixWord ++ tailWord_544822) baseStart_544822 baseEnd_544822 := by
    simpa [prefixWord, tailWord_544822, baseEnd_544822] using wordTrace_append hprefix tailTrace_544822
  have hstable : (prefixWord ++ tailWord_544822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544822).length < 2 ^ (prefixWord ++ tailWord_544822).sum := by decide
  have hdescent : baseEnd_544822 < baseStart_544822 := by decide
  rcases family_descends (prefixWord ++ tailWord_544822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544850 : List Nat := [3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_544850 : Nat := 118140960795 + 544850 * 2 ^ 59
def prefixEnd_544850 : Nat := 4983230072969 + 3 ^ 40 * 544850 * 2
def baseEnd_544850 : Nat := 82894795437718075724233

theorem tailTrace_544850 : CollatzResearch.WordTrace tailWord_544850 prefixEnd_544850 82894795437718075724233 := by
  unfold tailWord_544850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968078019027244454196001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13248208050739318544522669 4968078019027244454196001)
  ·
    refine ⟨3726058514270433340647001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4968078019027244454196001 3726058514270433340647001)
    ·
      refine ⟨2794543885702825005485251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3726058514270433340647001 2794543885702825005485251)
      ·
        refine ⟨4191815828554237508227877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794543885702825005485251 4191815828554237508227877)
        ·
          refine ⟨785965467853919532792727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4191815828554237508227877 785965467853919532792727)
          ·
            refine ⟨1178948201780879299189091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785965467853919532792727 1178948201780879299189091)
            ·
              refine ⟨1768422302671318948783637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178948201780879299189091 1768422302671318948783637)
              ·
                refine ⟨82894795437718075724233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1768422302671318948783637 82894795437718075724233)
                ·
                  rfl

theorem cell20_544850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_544850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544850 prefixEnd_544850 := by exact prefixLift 544850
  have htrace : WordTrace (prefixWord ++ tailWord_544850) baseStart_544850 baseEnd_544850 := by
    simpa [prefixWord, tailWord_544850, baseEnd_544850] using wordTrace_append hprefix tailTrace_544850
  have hstable : (prefixWord ++ tailWord_544850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544850).length < 2 ^ (prefixWord ++ tailWord_544850).sum := by decide
  have hdescent : baseEnd_544850 < baseStart_544850 := by decide
  rcases family_descends (prefixWord ++ tailWord_544850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544860 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_544860 : Nat := 118140960795 + 544860 * 2 ^ 59
def prefixEnd_544860 : Nat := 4983230072969 + 3 ^ 40 * 544860 * 2
def baseEnd_544860 : Nat := 248688950585638636839325

theorem tailTrace_544860 : CollatzResearch.WordTrace tailWord_544860 prefixEnd_544860 248688950585638636839325 := by
  unfold tailWord_544860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936338403036374762324017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13248451204048499683098689 9936338403036374762324017)
  ·
    refine ⟨7452253802277281071743013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9936338403036374762324017 7452253802277281071743013)
    ·
      refine ⟨1397297587926990200951815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7452253802277281071743013 1397297587926990200951815)
      ·
        refine ⟨2095946381890485301427723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397297587926990200951815 2095946381890485301427723)
        ·
          refine ⟨3143919572835727952141585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095946381890485301427723 3143919572835727952141585)
          ·
            refine ⟨2357939679626795964106189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3143919572835727952141585 2357939679626795964106189)
            ·
              refine ⟨884227379860048486539821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357939679626795964106189 884227379860048486539821)
              ·
                refine ⟨331585267447518182452433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884227379860048486539821 331585267447518182452433)
                ·
                  refine ⟨248688950585638636839325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331585267447518182452433 248688950585638636839325)
                  ·
                    rfl

theorem cell20_544860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_544860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544860 prefixEnd_544860 := by exact prefixLift 544860
  have htrace : WordTrace (prefixWord ++ tailWord_544860) baseStart_544860 baseEnd_544860 := by
    simpa [prefixWord, tailWord_544860, baseEnd_544860] using wordTrace_append hprefix tailTrace_544860
  have hstable : (prefixWord ++ tailWord_544860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544860).length < 2 ^ (prefixWord ++ tailWord_544860).sum := by decide
  have hdescent : baseEnd_544860 < baseStart_544860 := by decide
  rcases family_descends (prefixWord ++ tailWord_544860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544926 : List Nat := [4, 3, 1, 1, 3, 8]
def baseStart_544926 : Nat := 118140960795 + 544926 * 2 ^ 59
def prefixEnd_544926 : Nat := 4983230072969 + 3 ^ 40 * 544926 * 2
def baseEnd_544926 : Nat := 9211817584593916319965

theorem tailTrace_544926 : CollatzResearch.WordTrace tailWord_544926 prefixEnd_544926 9211817584593916319965 := by
  unfold tailWord_544926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484385502979205349568829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13250056015889095197700421 2484385502979205349568829)
  ·
    refine ⟨931644563617202006088311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2484385502979205349568829 931644563617202006088311)
    ·
      refine ⟨1397466845425803009132467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931644563617202006088311 1397466845425803009132467)
      ·
        refine ⟨2096200268138704513698701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397466845425803009132467 2096200268138704513698701)
        ·
          refine ⟨786075100552014192637013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2096200268138704513698701 786075100552014192637013)
          ·
            refine ⟨9211817584593916319965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 786075100552014192637013 9211817584593916319965)
            ·
              rfl

theorem cell20_544926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 8].length) (baseStart_544926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544926 prefixEnd_544926 := by exact prefixLift 544926
  have htrace : WordTrace (prefixWord ++ tailWord_544926) baseStart_544926 baseEnd_544926 := by
    simpa [prefixWord, tailWord_544926, baseEnd_544926] using wordTrace_append hprefix tailTrace_544926
  have hstable : (prefixWord ++ tailWord_544926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544926).length < 2 ^ (prefixWord ++ tailWord_544926).sum := by decide
  have hdescent : baseEnd_544926 < baseStart_544926 := by decide
  rcases family_descends (prefixWord ++ tailWord_544926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544932 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_544932 : Nat := 118140960795 + 544932 * 2 ^ 59
def prefixEnd_544932 : Nat := 4983230072969 + 3 ^ 40 * 544932 * 2
def baseEnd_544932 : Nat := 248721813347526386439031

theorem tailTrace_544932 : CollatzResearch.WordTrace tailWord_544932 prefixEnd_544932 248721813347526386439031 := by
  unfold tailWord_544932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937651430905952910634525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13250201907874603880846033 9937651430905952910634525)
  ·
    refine ⟨3726619286589732341487947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9937651430905952910634525 3726619286589732341487947)
    ·
      refine ⟨5589928929884598512231921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726619286589732341487947 5589928929884598512231921)
      ·
        refine ⟨4192446697413448884173941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5589928929884598512231921 4192446697413448884173941)
        ·
          refine ⟨393041877882510832891307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4192446697413448884173941 393041877882510832891307)
          ·
            refine ⟨589562816823766249336961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393041877882510832891307 589562816823766249336961)
            ·
              refine ⟨442172112617824687002721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589562816823766249336961 442172112617824687002721)
              ·
                refine ⟨331629084463368515252041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442172112617824687002721 331629084463368515252041)
                ·
                  refine ⟨248721813347526386439031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331629084463368515252041 248721813347526386439031)
                  ·
                    rfl

theorem cell20_544932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_544932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544932 prefixEnd_544932 := by exact prefixLift 544932
  have htrace : WordTrace (prefixWord ++ tailWord_544932) baseStart_544932 baseEnd_544932 := by
    simpa [prefixWord, tailWord_544932, baseEnd_544932] using wordTrace_append hprefix tailTrace_544932
  have hstable : (prefixWord ++ tailWord_544932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544932).length < 2 ^ (prefixWord ++ tailWord_544932).sum := by decide
  have hdescent : baseEnd_544932 < baseStart_544932 := by decide
  rcases family_descends (prefixWord ++ tailWord_544932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544933 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_544933 : Nat := 118140960795 + 544933 * 2 ^ 59
def prefixEnd_544933 : Nat := 4983230072969 + 3 ^ 40 * 544933 * 2
def baseEnd_544933 : Nat := 248722269774774827405693

theorem tailTrace_544933 : CollatzResearch.WordTrace tailWord_544933 prefixEnd_544933 248722269774774827405693 := by
  unfold tailWord_544933
  simp only [CollatzResearch.WordTrace]
  refine ⟨19875339334808282992055453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13250226223205521994703635 19875339334808282992055453)
  ·
    refine ⟨7453252250553106122020795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19875339334808282992055453 7453252250553106122020795)
    ·
      refine ⟨11179878375829659183031193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453252250553106122020795 11179878375829659183031193)
      ·
        refine ⟨8384908781872244387273395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179878375829659183031193 8384908781872244387273395)
        ·
          refine ⟨12577363172808366580910093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384908781872244387273395 12577363172808366580910093)
          ·
            refine ⟨4716511189803137467841285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12577363172808366580910093 4716511189803137467841285)
            ·
              refine ⟨884345848088088275220241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4716511189803137467841285 884345848088088275220241)
              ·
                refine ⟨663259386066066206415181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884345848088088275220241 663259386066066206415181)
                ·
                  refine ⟨248722269774774827405693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663259386066066206415181 248722269774774827405693)
                  ·
                    rfl

theorem cell20_544933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_544933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544933 prefixEnd_544933 := by exact prefixLift 544933
  have htrace : WordTrace (prefixWord ++ tailWord_544933) baseStart_544933 baseEnd_544933 := by
    simpa [prefixWord, tailWord_544933, baseEnd_544933] using wordTrace_append hprefix tailTrace_544933
  have hstable : (prefixWord ++ tailWord_544933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544933).length < 2 ^ (prefixWord ++ tailWord_544933).sum := by decide
  have hdescent : baseEnd_544933 < baseStart_544933 := by decide
  rcases family_descends (prefixWord ++ tailWord_544933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544974 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_544974 : Nat := 118140960795 + 544974 * 2 ^ 59
def prefixEnd_544974 : Nat := 4983230072969 + 3 ^ 40 * 544974 * 2
def baseEnd_544974 : Nat := 248740983291960907038859

theorem tailTrace_544974 : CollatzResearch.WordTrace tailWord_544974 prefixEnd_544974 248740983291960907038859 := by
  unfold tailWord_544974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484604340957468374287247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13251223151773164662865317 2484604340957468374287247)
  ·
    refine ⟨3726906511436202561430871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484604340957468374287247 3726906511436202561430871)
    ·
      refine ⟨5590359767154303842146307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726906511436202561430871 5590359767154303842146307)
      ·
        refine ⟨8385539650731455763219461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590359767154303842146307 8385539650731455763219461)
        ·
          refine ⟨1572288684512147955603649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8385539650731455763219461 1572288684512147955603649)
          ·
            refine ⟨1179216513384110966702737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572288684512147955603649 1179216513384110966702737)
            ·
              refine ⟨884412385038083225027053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179216513384110966702737 884412385038083225027053)
              ·
                refine ⟨331654644389281209385145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884412385038083225027053 331654644389281209385145)
                ·
                  refine ⟨248740983291960907038859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331654644389281209385145 248740983291960907038859)
                  ·
                    rfl

theorem cell20_544974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_544974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544974 prefixEnd_544974 := by exact prefixLift 544974
  have htrace : WordTrace (prefixWord ++ tailWord_544974) baseStart_544974 baseEnd_544974 := by
    simpa [prefixWord, tailWord_544974, baseEnd_544974] using wordTrace_append hprefix tailTrace_544974
  have hstable : (prefixWord ++ tailWord_544974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544974).length < 2 ^ (prefixWord ++ tailWord_544974).sum := by decide
  have hdescent : baseEnd_544974 < baseStart_544974 := by decide
  rcases family_descends (prefixWord ++ tailWord_544974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544992 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_544992 : Nat := 118140960795 + 544992 * 2 ^ 59
def prefixEnd_544992 : Nat := 4983230072969 + 3 ^ 40 * 544992 * 2
def baseEnd_544992 : Nat := 248749198982432844438785

theorem tailTrace_544992 : CollatzResearch.WordTrace tailWord_544992 prefixEnd_544992 248749198982432844438785 := by
  unfold tailWord_544992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938745620797268034226615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13251660827729690712302153 9938745620797268034226615)
  ·
    refine ⟨14908118431195902051339923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9938745620797268034226615 14908118431195902051339923)
    ·
      refine ⟨22362177646793853077009885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14908118431195902051339923 22362177646793853077009885)
      ·
        refine ⟨8385816617547694903878707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22362177646793853077009885 8385816617547694903878707)
        ·
          refine ⟨12578724926321542355818061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385816617547694903878707 12578724926321542355818061)
          ·
            refine ⟨4717021847370578383431773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12578724926321542355818061 4717021847370578383431773)
            ·
              refine ⟨1768883192763966893786915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4717021847370578383431773 1768883192763966893786915)
              ·
                refine ⟨2653324789145950340680373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768883192763966893786915 2653324789145950340680373)
                ·
                  refine ⟨248749198982432844438785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2653324789145950340680373 248749198982432844438785)
                  ·
                    rfl

theorem cell20_544992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_544992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_544992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_544992 prefixEnd_544992 := by exact prefixLift 544992
  have htrace : WordTrace (prefixWord ++ tailWord_544992) baseStart_544992 baseEnd_544992 := by
    simpa [prefixWord, tailWord_544992, baseEnd_544992] using wordTrace_append hprefix tailTrace_544992
  have hstable : (prefixWord ++ tailWord_544992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544992).length < 2 ^ (prefixWord ++ tailWord_544992).sum := by decide
  have hdescent : baseEnd_544992 < baseStart_544992 := by decide
  rcases family_descends (prefixWord ++ tailWord_544992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545005 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_545005 : Nat := 118140960795 + 545005 * 2 ^ 59
def prefixEnd_545005 : Nat := 4983230072969 + 3 ^ 40 * 545005 * 2
def baseEnd_545005 : Nat := 248755132536662577005399

theorem tailTrace_545005 : CollatzResearch.WordTrace tailWord_545005 prefixEnd_545005 248755132536662577005399 := by
  unfold tailWord_545005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19877965390547439288676469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13251976927031626192450979 19877965390547439288676469)
  ·
    refine ⟨1863559255363822433313419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19877965390547439288676469 1863559255363822433313419)
    ·
      refine ⟨2795338883045733649970129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863559255363822433313419 2795338883045733649970129)
      ·
        refine ⟨2096504162284300237477597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795338883045733649970129 2096504162284300237477597)
        ·
          refine ⟨786189060856612589054099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2096504162284300237477597 786189060856612589054099)
          ·
            refine ⟨1179283591284918883581149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786189060856612589054099 1179283591284918883581149)
            ·
              refine ⟨442231346731844581342931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179283591284918883581149 442231346731844581342931)
              ·
                refine ⟨663347020097766872014397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442231346731844581342931 663347020097766872014397)
                ·
                  refine ⟨248755132536662577005399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663347020097766872014397 248755132536662577005399)
                  ·
                    rfl

theorem cell20_545005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_545005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545005 prefixEnd_545005 := by exact prefixLift 545005
  have htrace : WordTrace (prefixWord ++ tailWord_545005) baseStart_545005 baseEnd_545005 := by
    simpa [prefixWord, tailWord_545005, baseEnd_545005] using wordTrace_append hprefix tailTrace_545005
  have hstable : (prefixWord ++ tailWord_545005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545005).length < 2 ^ (prefixWord ++ tailWord_545005).sum := by decide
  have hdescent : baseEnd_545005 < baseStart_545005 := by decide
  rcases family_descends (prefixWord ++ tailWord_545005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545033 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 2]
def baseStart_545033 : Nat := 118140960795 + 545033 * 2 ^ 59
def prefixEnd_545033 : Nat := 4983230072969 + 3 ^ 40 * 545033 * 2
def baseEnd_545033 : Nat := 248767912499618924071951

theorem tailTrace_545033 : CollatzResearch.WordTrace tailWord_545033 prefixEnd_545033 248767912499618924071951 := by
  unfold tailWord_545033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878986634446000070695753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13252657756297333380463835 19878986634446000070695753)
  ·
    refine ⟨14909239975834500053021815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19878986634446000070695753 14909239975834500053021815)
    ·
      refine ⟨22363859963751750079532723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14909239975834500053021815 22363859963751750079532723)
      ·
        refine ⟨33545789945627625119299085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22363859963751750079532723 33545789945627625119299085)
        ·
          refine ⟨12579671229610359419737157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33545789945627625119299085 12579671229610359419737157)
          ·
            refine ⟨2358688355551942391200717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12579671229610359419737157 2358688355551942391200717)
            ·
              refine ⟨884508133331978396700269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2358688355551942391200717 884508133331978396700269)
              ·
                refine ⟨331690549999491898762601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884508133331978396700269 331690549999491898762601)
                ·
                  refine ⟨248767912499618924071951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331690549999491898762601 248767912499618924071951)
                  ·
                    rfl

theorem cell20_545033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_545033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545033 prefixEnd_545033 := by exact prefixLift 545033
  have htrace : WordTrace (prefixWord ++ tailWord_545033) baseStart_545033 baseEnd_545033 := by
    simpa [prefixWord, tailWord_545033, baseEnd_545033] using wordTrace_append hprefix tailTrace_545033
  have hstable : (prefixWord ++ tailWord_545033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545033).length < 2 ^ (prefixWord ++ tailWord_545033).sum := by decide
  have hdescent : baseEnd_545033 < baseStart_545033 := by decide
  rcases family_descends (prefixWord ++ tailWord_545033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545050 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_545050 : Nat := 118140960795 + 545050 * 2 ^ 59
def prefixEnd_545050 : Nat := 4983230072969 + 3 ^ 40 * 545050 * 2
def baseEnd_545050 : Nat := 248775671762842420505215

theorem tailTrace_545050 : CollatzResearch.WordTrace tailWord_545050 prefixEnd_545050 248775671762842420505215 := by
  unfold tailWord_545050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969901668846102993516151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13253071116922941316043069 4969901668846102993516151)
  ·
    refine ⟨7454852503269154490274227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4969901668846102993516151 7454852503269154490274227)
    ·
      refine ⟨11182278754903731735411341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7454852503269154490274227 11182278754903731735411341)
      ·
        refine ⟨4193354533088899400779253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11182278754903731735411341 4193354533088899400779253)
        ·
          refine ⟨393126987477084318823055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4193354533088899400779253 393126987477084318823055)
          ·
            refine ⟨589690481215626478234583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393126987477084318823055 589690481215626478234583)
            ·
              refine ⟨884535721823439717351875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589690481215626478234583 884535721823439717351875)
              ·
                refine ⟨1326803582735159576027813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884535721823439717351875 1326803582735159576027813)
                ·
                  refine ⟨248775671762842420505215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326803582735159576027813 248775671762842420505215)
                  ·
                    rfl

theorem cell20_545050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_545050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545050 prefixEnd_545050 := by exact prefixLift 545050
  have htrace : WordTrace (prefixWord ++ tailWord_545050) baseStart_545050 baseEnd_545050 := by
    simpa [prefixWord, tailWord_545050, baseEnd_545050] using wordTrace_append hprefix tailTrace_545050
  have hstable : (prefixWord ++ tailWord_545050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545050).length < 2 ^ (prefixWord ++ tailWord_545050).sum := by decide
  have hdescent : baseEnd_545050 < baseStart_545050 := by decide
  rcases family_descends (prefixWord ++ tailWord_545050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545064 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_545064 : Nat := 118140960795 + 545064 * 2 ^ 59
def prefixEnd_545064 : Nat := 4983230072969 + 3 ^ 40 * 545064 * 2
def baseEnd_545064 : Nat := 248782061744320594038491

theorem tailTrace_545064 : CollatzResearch.WordTrace tailWord_545064 prefixEnd_545064 248782061744320594038491 := by
  unfold tailWord_545064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940058648666846182537123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13253411531555794910049497 9940058648666846182537123)
  ·
    refine ⟨14910087973000269273805685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9940058648666846182537123 14910087973000269273805685)
    ·
      refine ⟨1397820747468775244419283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14910087973000269273805685 1397820747468775244419283)
      ·
        refine ⟨2096731121203162866628925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397820747468775244419283 2096731121203162866628925)
        ·
          refine ⟨786274170451186074985847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2096731121203162866628925 786274170451186074985847)
          ·
            refine ⟨1179411255676779112478771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786274170451186074985847 1179411255676779112478771)
            ·
              refine ⟨1769116883515168668718157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179411255676779112478771 1769116883515168668718157)
              ·
                refine ⟨663418831318188250769309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769116883515168668718157 663418831318188250769309)
                ·
                  refine ⟨248782061744320594038491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663418831318188250769309 248782061744320594038491)
                  ·
                    rfl

theorem cell20_545064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_545064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545064 prefixEnd_545064 := by exact prefixLift 545064
  have htrace : WordTrace (prefixWord ++ tailWord_545064) baseStart_545064 baseEnd_545064 := by
    simpa [prefixWord, tailWord_545064, baseEnd_545064] using wordTrace_append hprefix tailTrace_545064
  have hstable : (prefixWord ++ tailWord_545064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545064).length < 2 ^ (prefixWord ++ tailWord_545064).sum := by decide
  have hdescent : baseEnd_545064 < baseStart_545064 := by decide
  rcases family_descends (prefixWord ++ tailWord_545064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545075 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_545075 : Nat := 118140960795 + 545075 * 2 ^ 59
def prefixEnd_545075 : Nat := 4983230072969 + 3 ^ 40 * 545075 * 2
def baseEnd_545075 : Nat := 248787082444053444671779

theorem tailTrace_545075 : CollatzResearch.WordTrace tailWord_545075 prefixEnd_545075 248787082444053444671779 := by
  unfold tailWord_545075
  simp only [CollatzResearch.WordTrace]
  refine ⟨19880518500293841243724679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13253679000195894162483119 19880518500293841243724679)
  ·
    refine ⟨29820777750440761865587019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19880518500293841243724679 29820777750440761865587019)
    ·
      refine ⟨44731166625661142798380529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29820777750440761865587019 44731166625661142798380529)
      ·
        refine ⟨33548374969245857098785397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44731166625661142798380529 33548374969245857098785397)
        ·
          refine ⟨3145160153366799103011131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33548374969245857098785397 3145160153366799103011131)
          ·
            refine ⟨4717740230050198654516697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145160153366799103011131 4717740230050198654516697)
            ·
              refine ⟨3538305172537648990887523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717740230050198654516697 3538305172537648990887523)
              ·
                refine ⟨5307457758806473486331285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538305172537648990887523 5307457758806473486331285)
                ·
                  refine ⟨248787082444053444671779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5307457758806473486331285 248787082444053444671779)
                  ·
                    rfl

theorem cell20_545075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_545075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545075 prefixEnd_545075 := by exact prefixLift 545075
  have htrace : WordTrace (prefixWord ++ tailWord_545075) baseStart_545075 baseEnd_545075 := by
    simpa [prefixWord, tailWord_545075, baseEnd_545075] using wordTrace_append hprefix tailTrace_545075
  have hstable : (prefixWord ++ tailWord_545075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545075).length < 2 ^ (prefixWord ++ tailWord_545075).sum := by decide
  have hdescent : baseEnd_545075 < baseStart_545075 := by decide
  rcases family_descends (prefixWord ++ tailWord_545075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545106 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_545106 : Nat := 118140960795 + 545106 * 2 ^ 59
def prefixEnd_545106 : Nat := 4983230072969 + 3 ^ 40 * 545106 * 2
def baseEnd_545106 : Nat := 248801231688755114638319

theorem tailTrace_545106 : CollatzResearch.WordTrace tailWord_545106 prefixEnd_545106 248801231688755114638319 := by
  unfold tailWord_545106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970412290795383384525793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13254432775454355692068781 4970412290795383384525793)
  ·
    refine ⟨3727809218096537538394345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4970412290795383384525793 3727809218096537538394345)
    ·
      refine ⟨2795856913572403153795759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3727809218096537538394345 2795856913572403153795759)
      ·
        refine ⟨4193785370358604730693639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795856913572403153795759 4193785370358604730693639)
        ·
          refine ⟨6290678055537907096040459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193785370358604730693639 6290678055537907096040459)
          ·
            refine ⟨9436017083306860644060689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290678055537907096040459 9436017083306860644060689)
            ·
              refine ⟨7077012812480145483045517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9436017083306860644060689 7077012812480145483045517)
              ·
                refine ⟨2653879804680054556142069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7077012812480145483045517 2653879804680054556142069)
                ·
                  refine ⟨248801231688755114638319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2653879804680054556142069 248801231688755114638319)
                  ·
                    rfl

theorem cell20_545106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_545106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545106 prefixEnd_545106 := by exact prefixLift 545106
  have htrace : WordTrace (prefixWord ++ tailWord_545106) baseStart_545106 baseEnd_545106 := by
    simpa [prefixWord, tailWord_545106, baseEnd_545106] using wordTrace_append hprefix tailTrace_545106
  have hstable : (prefixWord ++ tailWord_545106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545106).length < 2 ^ (prefixWord ++ tailWord_545106).sum := by decide
  have hdescent : baseEnd_545106 < baseStart_545106 := by decide
  rcases family_descends (prefixWord ++ tailWord_545106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545113 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_545113 : Nat := 118140960795 + 545113 * 2 ^ 59
def prefixEnd_545113 : Nat := 4983230072969 + 3 ^ 40 * 545113 * 2
def baseEnd_545113 : Nat := 248804426679494201404957

theorem tailTrace_545113 : CollatzResearch.WordTrace tailWord_545113 prefixEnd_545113 248804426679494201404957 := by
  unfold tailWord_545113
  simp only [CollatzResearch.WordTrace]
  refine ⟨19881904474156173733607993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13254602982770782489071995 19881904474156173733607993)
  ·
    refine ⟨14911428355617130300205995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19881904474156173733607993 14911428355617130300205995)
    ·
      refine ⟨22367142533425695450308993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14911428355617130300205995 22367142533425695450308993)
      ·
        refine ⟨16775356900069271587731745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22367142533425695450308993 16775356900069271587731745)
        ·
          refine ⟨12581517675051953690798809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16775356900069271587731745 12581517675051953690798809)
          ·
            refine ⟨9436138256288965268099107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12581517675051953690798809 9436138256288965268099107)
            ·
              refine ⟨14154207384433447902148661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9436138256288965268099107 14154207384433447902148661)
              ·
                refine ⟨1326956942290635740826437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14154207384433447902148661 1326956942290635740826437)
                ·
                  refine ⟨248804426679494201404957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326956942290635740826437 248804426679494201404957)
                  ·
                    rfl

theorem cell20_545113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_545113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545113 prefixEnd_545113 := by exact prefixLift 545113
  have htrace : WordTrace (prefixWord ++ tailWord_545113) baseStart_545113 baseEnd_545113 := by
    simpa [prefixWord, tailWord_545113, baseEnd_545113] using wordTrace_append hprefix tailTrace_545113
  have hstable : (prefixWord ++ tailWord_545113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545113).length < 2 ^ (prefixWord ++ tailWord_545113).sum := by decide
  have hdescent : baseEnd_545113 < baseStart_545113 := by decide
  rcases family_descends (prefixWord ++ tailWord_545113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545130 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_545130 : Nat := 118140960795 + 545130 * 2 ^ 59
def prefixEnd_545130 : Nat := 4983230072969 + 3 ^ 40 * 545130 * 2
def baseEnd_545130 : Nat := 248812185942717697838221

theorem tailTrace_545130 : CollatzResearch.WordTrace tailWord_545130 prefixEnd_545130 248812185942717697838221 := by
  unfold tailWord_545130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970631128773646409244211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13255016343396390424651229 4970631128773646409244211)
  ·
    refine ⟨7455946693160469613866317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4970631128773646409244211 7455946693160469613866317)
    ·
      refine ⟨2795980009935176105199869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7455946693160469613866317 2795980009935176105199869)
      ·
        refine ⟨1048492503725691039449951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2795980009935176105199869 1048492503725691039449951)
        ·
          refine ⟨1572738755588536559174927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048492503725691039449951 1572738755588536559174927)
          ·
            refine ⟨2359108133382804838762391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572738755588536559174927 2359108133382804838762391)
            ·
              refine ⟨3538662200074207258143587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359108133382804838762391 3538662200074207258143587)
              ·
                refine ⟨5307993300111310887215381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538662200074207258143587 5307993300111310887215381)
                ·
                  refine ⟨248812185942717697838221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5307993300111310887215381 248812185942717697838221)
                  ·
                    rfl

theorem cell20_545130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_545130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545130 prefixEnd_545130 := by exact prefixLift 545130
  have htrace : WordTrace (prefixWord ++ tailWord_545130) baseStart_545130 baseEnd_545130 := by
    simpa [prefixWord, tailWord_545130, baseEnd_545130] using wordTrace_append hprefix tailTrace_545130
  have hstable : (prefixWord ++ tailWord_545130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545130).length < 2 ^ (prefixWord ++ tailWord_545130).sum := by decide
  have hdescent : baseEnd_545130 < baseStart_545130 := by decide
  rcases family_descends (prefixWord ++ tailWord_545130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545147 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 2]
def baseStart_545147 : Nat := 118140960795 + 545147 * 2 ^ 59
def prefixEnd_545147 : Nat := 4983230072969 + 3 ^ 40 * 545147 * 2
def baseEnd_545147 : Nat := 248819945205941194271485

theorem tailTrace_545147 : CollatzResearch.WordTrace tailWord_545147 prefixEnd_545147 248819945205941194271485 := by
  unfold tailWord_545147
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883144556032997540345695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13255429704021998360230463 19883144556032997540345695)
  ·
    refine ⟨29824716834049496310518543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883144556032997540345695 29824716834049496310518543)
    ·
      refine ⟨44737075251074244465777815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29824716834049496310518543 44737075251074244465777815)
      ·
        refine ⟨67105612876611366698666723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44737075251074244465777815 67105612876611366698666723)
        ·
          refine ⟨100658419314917050048000085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67105612876611366698666723 100658419314917050048000085)
          ·
            refine ⟨1179590851346684180250001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 100658419314917050048000085 1179590851346684180250001)
            ·
              refine ⟨884693138510013135187501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179590851346684180250001 884693138510013135187501)
              ·
                refine ⟨331759926941254925695313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884693138510013135187501 331759926941254925695313)
                ·
                  refine ⟨248819945205941194271485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331759926941254925695313 248819945205941194271485)
                  ·
                    rfl

theorem cell20_545147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2].length) (baseStart_545147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545147 prefixEnd_545147 := by exact prefixLift 545147
  have htrace : WordTrace (prefixWord ++ tailWord_545147) baseStart_545147 baseEnd_545147 := by
    simpa [prefixWord, tailWord_545147, baseEnd_545147] using wordTrace_append hprefix tailTrace_545147
  have hstable : (prefixWord ++ tailWord_545147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545147).length < 2 ^ (prefixWord ++ tailWord_545147).sum := by decide
  have hdescent : baseEnd_545147 < baseStart_545147 := by decide
  rcases family_descends (prefixWord ++ tailWord_545147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545161 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_545161 : Nat := 118140960795 + 545161 * 2 ^ 59
def prefixEnd_545161 : Nat := 4983230072969 + 3 ^ 40 * 545161 * 2
def baseEnd_545161 : Nat := 248826335187419367804761

theorem tailTrace_545161 : CollatzResearch.WordTrace tailWord_545161 prefixEnd_545161 248826335187419367804761 := by
  unfold tailWord_545161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883655177982277931355337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13255770118654851954236891 19883655177982277931355337)
  ·
    refine ⟨14912741383486708448516503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19883655177982277931355337 14912741383486708448516503)
    ·
      refine ⟨22369112075230062672774755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14912741383486708448516503 22369112075230062672774755)
      ·
        refine ⟨33553668112845094009162133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22369112075230062672774755 33553668112845094009162133)
        ·
          refine ⟨1572828192789613781679475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33553668112845094009162133 1572828192789613781679475)
          ·
            refine ⟨2359242289184420672519213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572828192789613781679475 2359242289184420672519213)
            ·
              refine ⟨884715858444157752194705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2359242289184420672519213 884715858444157752194705)
              ·
                refine ⟨663536893833118314146029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884715858444157752194705 663536893833118314146029)
                ·
                  refine ⟨248826335187419367804761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663536893833118314146029 248826335187419367804761)
                  ·
                    rfl

theorem cell20_545161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_545161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545161 prefixEnd_545161 := by exact prefixLift 545161
  have htrace : WordTrace (prefixWord ++ tailWord_545161) baseStart_545161 baseEnd_545161 := by
    simpa [prefixWord, tailWord_545161, baseEnd_545161] using wordTrace_append hprefix tailTrace_545161
  have hstable : (prefixWord ++ tailWord_545161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545161).length < 2 ^ (prefixWord ++ tailWord_545161).sum := by decide
  have hdescent : baseEnd_545161 < baseStart_545161 := by decide
  rcases family_descends (prefixWord ++ tailWord_545161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545178 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_545178 : Nat := 118140960795 + 545178 * 2 ^ 59
def prefixEnd_545178 : Nat := 4983230072969 + 3 ^ 40 * 545178 * 2
def baseEnd_545178 : Nat := 248834094450642864238025

theorem tailTrace_545178 : CollatzResearch.WordTrace tailWord_545178 prefixEnd_545178 248834094450642864238025 := by
  unfold tailWord_545178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971068804730172458681047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13256183479280459889816125 4971068804730172458681047)
  ·
    refine ⟨7456603207095258688021571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971068804730172458681047 7456603207095258688021571)
    ·
      refine ⟨11184904810642888032032357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7456603207095258688021571 11184904810642888032032357)
      ·
        refine ⟨2097169651995541506006067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11184904810642888032032357 2097169651995541506006067)
        ·
          refine ⟨3145754477993312259009101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097169651995541506006067 3145754477993312259009101)
          ·
            refine ⟨1179657929247492097128413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3145754477993312259009101 1179657929247492097128413)
            ·
              refine ⟨442371723467809536423155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179657929247492097128413 442371723467809536423155)
              ·
                refine ⟨663557585201714304634733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442371723467809536423155 663557585201714304634733)
                ·
                  refine ⟨248834094450642864238025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663557585201714304634733 248834094450642864238025)
                  ·
                    rfl

theorem cell20_545178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_545178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545178 prefixEnd_545178 := by exact prefixLift 545178
  have htrace : WordTrace (prefixWord ++ tailWord_545178) baseStart_545178 baseEnd_545178 := by
    simpa [prefixWord, tailWord_545178, baseEnd_545178] using wordTrace_append hprefix tailTrace_545178
  have hstable : (prefixWord ++ tailWord_545178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545178).length < 2 ^ (prefixWord ++ tailWord_545178).sum := by decide
  have hdescent : baseEnd_545178 < baseStart_545178 := by decide
  rcases family_descends (prefixWord ++ tailWord_545178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545189 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_545189 : Nat := 118140960795 + 545189 * 2 ^ 59
def prefixEnd_545189 : Nat := 4983230072969 + 3 ^ 40 * 545189 * 2
def baseEnd_545189 : Nat := 248839115150375714871313

theorem tailTrace_545189 : CollatzResearch.WordTrace tailWord_545189 prefixEnd_545189 248839115150375714871313 := by
  unfold tailWord_545189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19884676421880838713374621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13256450947920559142249747 19884676421880838713374621)
  ·
    refine ⟨7456753658205314517515483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19884676421880838713374621 7456753658205314517515483)
    ·
      refine ⟨11185130487307971776273225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7456753658205314517515483 11185130487307971776273225)
      ·
        refine ⟨8388847865480978832204919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11185130487307971776273225 8388847865480978832204919)
        ·
          refine ⟨12583271798221468248307379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388847865480978832204919 12583271798221468248307379)
          ·
            refine ⟨18874907697332202372461069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583271798221468248307379 18874907697332202372461069)
            ·
              refine ⟨7078090386499575889672901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18874907697332202372461069 7078090386499575889672901)
              ·
                refine ⟨1327141947468670479313669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7078090386499575889672901 1327141947468670479313669)
                ·
                  refine ⟨248839115150375714871313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327141947468670479313669 248839115150375714871313)
                  ·
                    rfl

theorem cell20_545189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_545189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545189 prefixEnd_545189 := by exact prefixLift 545189
  have htrace : WordTrace (prefixWord ++ tailWord_545189) baseStart_545189 baseEnd_545189 := by
    simpa [prefixWord, tailWord_545189, baseEnd_545189] using wordTrace_append hprefix tailTrace_545189
  have hstable : (prefixWord ++ tailWord_545189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545189).length < 2 ^ (prefixWord ++ tailWord_545189).sum := by decide
  have hdescent : baseEnd_545189 < baseStart_545189 := by decide
  rcases family_descends (prefixWord ++ tailWord_545189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545192 : List Nat := [2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_545192 : Nat := 118140960795 + 545192 * 2 ^ 59
def prefixEnd_545192 : Nat := 4983230072969 + 3 ^ 40 * 545192 * 2
def baseEnd_545192 : Nat := 82946828144040345923767

theorem tailTrace_545192 : CollatzResearch.WordTrace tailWord_545192 prefixEnd_545192 82946828144040345923767 := by
  unfold tailWord_545192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9942392920434985112866915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13256523893913313483822553 9942392920434985112866915)
  ·
    refine ⟨14913589380652477669300373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9942392920434985112866915 14913589380652477669300373)
    ·
      refine ⟨699074502218084890748455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14913589380652477669300373 699074502218084890748455)
      ·
        refine ⟨1048611753327127336122683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699074502218084890748455 1048611753327127336122683)
        ·
          refine ⟨1572917629990691004184025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048611753327127336122683 1572917629990691004184025)
          ·
            refine ⟨1179688222493018253138019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572917629990691004184025 1179688222493018253138019)
            ·
              refine ⟨1769532333739527379707029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179688222493018253138019 1769532333739527379707029)
              ·
                refine ⟨82946828144040345923767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1769532333739527379707029 82946828144040345923767)
                ·
                  rfl

theorem cell20_545192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_545192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545192 prefixEnd_545192 := by exact prefixLift 545192
  have htrace : WordTrace (prefixWord ++ tailWord_545192) baseStart_545192 baseEnd_545192 := by
    simpa [prefixWord, tailWord_545192, baseEnd_545192] using wordTrace_append hprefix tailTrace_545192
  have hstable : (prefixWord ++ tailWord_545192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545192).length < 2 ^ (prefixWord ++ tailWord_545192).sum := by decide
  have hdescent : baseEnd_545192 < baseStart_545192 := by decide
  rcases family_descends (prefixWord ++ tailWord_545192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545213 : List Nat := [1, 4, 1, 2, 2, 4, 6]
def baseStart_545213 : Nat := 118140960795 + 545213 * 2 ^ 59
def prefixEnd_545213 : Nat := 4983230072969 + 3 ^ 40 * 545213 * 2
def baseEnd_545213 : Nat := 27650007711593144230135

theorem tailTrace_545213 : CollatzResearch.WordTrace tailWord_545213 prefixEnd_545213 27650007711593144230135 := by
  unfold tailWord_545213
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885551773793890812248293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13257034515862593874832195 19885551773793890812248293)
  ·
    refine ⟨3728540957586354527296555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19885551773793890812248293 3728540957586354527296555)
    ·
      refine ⟨5592811436379531790944833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728540957586354527296555 5592811436379531790944833)
      ·
        refine ⟨4194608577284648843208625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592811436379531790944833 4194608577284648843208625)
        ·
          refine ⟨3145956432963486632406469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4194608577284648843208625 3145956432963486632406469)
          ·
            refine ⟨589866831180653743576213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3145956432963486632406469 589866831180653743576213)
            ·
              refine ⟨27650007711593144230135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 589866831180653743576213 27650007711593144230135)
              ·
                rfl

theorem cell20_545213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_545213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545213 prefixEnd_545213 := by exact prefixLift 545213
  have htrace : WordTrace (prefixWord ++ tailWord_545213) baseStart_545213 baseEnd_545213 := by
    simpa [prefixWord, tailWord_545213, baseEnd_545213] using wordTrace_append hprefix tailTrace_545213
  have hstable : (prefixWord ++ tailWord_545213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545213).length < 2 ^ (prefixWord ++ tailWord_545213).sum := by decide
  have hdescent : baseEnd_545213 < baseStart_545213 := by decide
  rcases family_descends (prefixWord ++ tailWord_545213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545237 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_545237 : Nat := 118140960795 + 545237 * 2 ^ 59
def prefixEnd_545237 : Nat := 4983230072969 + 3 ^ 40 * 545237 * 2
def baseEnd_545237 : Nat := 248861023658300881271117

theorem tailTrace_545237 : CollatzResearch.WordTrace tailWord_545237 prefixEnd_545237 248861023658300881271117 := by
  unfold tailWord_545237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19886427125706942911121965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13257618083804628607414643 19886427125706942911121965)
  ·
    refine ⟨7457410172140103591670737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19886427125706942911121965 7457410172140103591670737)
    ·
      refine ⟨5593057629105077693753053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457410172140103591670737 5593057629105077693753053)
      ·
        refine ⟨2097396610914404135157395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5593057629105077693753053 2097396610914404135157395)
        ·
          refine ⟨3146094916371606202736093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097396610914404135157395 3146094916371606202736093)
          ·
            refine ⟨1179785593639352326026035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3146094916371606202736093 1179785593639352326026035)
            ·
              refine ⟨1769678390459028489039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179785593639352326026035 1769678390459028489039053)
              ·
                refine ⟨663629396422135683389645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769678390459028489039053 663629396422135683389645)
                ·
                  refine ⟨248861023658300881271117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663629396422135683389645 248861023658300881271117)
                  ·
                    rfl

theorem cell20_545237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_545237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545237 prefixEnd_545237 := by exact prefixLift 545237
  have htrace : WordTrace (prefixWord ++ tailWord_545237) baseStart_545237 baseEnd_545237 := by
    simpa [prefixWord, tailWord_545237, baseEnd_545237] using wordTrace_append hprefix tailTrace_545237
  have hstable : (prefixWord ++ tailWord_545237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545237).length < 2 ^ (prefixWord ++ tailWord_545237).sum := by decide
  have hdescent : baseEnd_545237 < baseStart_545237 := by decide
  rcases family_descends (prefixWord ++ tailWord_545237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545365 : List Nat := [1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_545365 : Nat := 118140960795 + 545365 * 2 ^ 59
def prefixEnd_545365 : Nat := 4983230072969 + 3 ^ 40 * 545365 * 2
def baseEnd_545365 : Nat := 82973148782033775001309

theorem tailTrace_545365 : CollatzResearch.WordTrace tailWord_545365 prefixEnd_545365 82973148782033775001309 := by
  unfold tailWord_545365
  simp only [CollatzResearch.WordTrace]
  refine ⟨19891095669243220771781549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13260730446162147181187699 19891095669243220771781549)
  ·
    refine ⟨7459160875966207789418081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19891095669243220771781549 7459160875966207789418081)
    ·
      refine ⟨5594370656974655842063561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7459160875966207789418081 5594370656974655842063561)
      ·
        refine ⟨4195777992730991881547671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5594370656974655842063561 4195777992730991881547671)
        ·
          refine ⟨6293666989096487822321507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195777992730991881547671 6293666989096487822321507)
          ·
            refine ⟨9440500483644731733482261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293666989096487822321507 9440500483644731733482261)
            ·
              refine ⟨442523460170846800006981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9440500483644731733482261 442523460170846800006981)
              ·
                refine ⟨82973148782033775001309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442523460170846800006981 82973148782033775001309)
                ·
                  rfl

theorem cell20_545365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_545365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545365 prefixEnd_545365 := by exact prefixLift 545365
  have htrace : WordTrace (prefixWord ++ tailWord_545365) baseStart_545365 baseEnd_545365 := by
    simpa [prefixWord, tailWord_545365, baseEnd_545365] using wordTrace_append hprefix tailTrace_545365
  have hstable : (prefixWord ++ tailWord_545365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545365).length < 2 ^ (prefixWord ++ tailWord_545365).sum := by decide
  have hdescent : baseEnd_545365 < baseStart_545365 := by decide
  rcases family_descends (prefixWord ++ tailWord_545365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545392 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_545392 : Nat := 118140960795 + 545392 * 2 ^ 59
def prefixEnd_545392 : Nat := 4983230072969 + 3 ^ 40 * 545392 * 2
def baseEnd_545392 : Nat := 248931769881809231103817

theorem tailTrace_545392 : CollatzResearch.WordTrace tailWord_545392 prefixEnd_545392 248931769881809231103817 := by
  unfold tailWord_545392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9946040220072702191507215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13261386960096936255342953 9946040220072702191507215)
  ·
    refine ⟨14919060330109053287260823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9946040220072702191507215 14919060330109053287260823)
    ·
      refine ⟨22378590495163579930891235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14919060330109053287260823 22378590495163579930891235)
      ·
        refine ⟨33567885742745369896336853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22378590495163579930891235 33567885742745369896336853)
        ·
          refine ⟨786747322095594606945395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33567885742745369896336853 786747322095594606945395)
          ·
            refine ⟨1180120983143391910418093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786747322095594606945395 1180120983143391910418093)
            ·
              refine ⟨442545368678771966406785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1180120983143391910418093 442545368678771966406785)
              ·
                refine ⟨331909026509078974805089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442545368678771966406785 331909026509078974805089)
                ·
                  refine ⟨248931769881809231103817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331909026509078974805089 248931769881809231103817)
                  ·
                    rfl

theorem cell20_545392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_545392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545392 prefixEnd_545392 := by exact prefixLift 545392
  have htrace : WordTrace (prefixWord ++ tailWord_545392) baseStart_545392 baseEnd_545392 := by
    simpa [prefixWord, tailWord_545392, baseEnd_545392] using wordTrace_append hprefix tailTrace_545392
  have hstable : (prefixWord ++ tailWord_545392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545392).length < 2 ^ (prefixWord ++ tailWord_545392).sum := by decide
  have hdescent : baseEnd_545392 < baseStart_545392 := by decide
  rcases family_descends (prefixWord ++ tailWord_545392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545441 : List Nat := [1, 2, 3, 3, 4, 7]
def baseStart_545441 : Nat := 118140960795 + 545441 * 2 ^ 59
def prefixEnd_545441 : Nat := 4983230072969 + 3 ^ 40 * 545441 * 2
def baseEnd_545441 : Nat := 9220523511740105128529

theorem tailTrace_545441 : CollatzResearch.WordTrace tailWord_545441 prefixEnd_545441 9220523511740105128529 := by
  unfold tailWord_545441
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893867616967885751548177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13262578411311923834365451 19893867616967885751548177)
  ·
    refine ⟨14920400712725914313661133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19893867616967885751548177 14920400712725914313661133)
    ·
      refine ⟨5595150267272217867622925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14920400712725914313661133 5595150267272217867622925)
      ·
        refine ⟨2098181350227081700358597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5595150267272217867622925 2098181350227081700358597)
        ·
          refine ⟨393409003167577818817237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2098181350227081700358597 393409003167577818817237)
          ·
            refine ⟨9220523511740105128529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 393409003167577818817237 9220523511740105128529)
            ·
              rfl

theorem cell20_545441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 7].length) (baseStart_545441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545441 prefixEnd_545441 := by exact prefixLift 545441
  have htrace : WordTrace (prefixWord ++ tailWord_545441) baseStart_545441 baseEnd_545441 := by
    simpa [prefixWord, tailWord_545441, baseEnd_545441] using wordTrace_append hprefix tailTrace_545441
  have hstable : (prefixWord ++ tailWord_545441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545441).length < 2 ^ (prefixWord ++ tailWord_545441).sum := by decide
  have hdescent : baseEnd_545441 < baseStart_545441 := by decide
  rcases family_descends (prefixWord ++ tailWord_545441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545485 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 2]
def baseStart_545485 : Nat := 118140960795 + 545485 * 2 ^ 59
def prefixEnd_545485 : Nat := 4983230072969 + 3 ^ 40 * 545485 * 2
def baseEnd_545485 : Nat := 248974217615914241003437

theorem tailTrace_545485 : CollatzResearch.WordTrace tailWord_545485 prefixEnd_545485 248974217615914241003437 := by
  unfold tailWord_545485
  simp only [CollatzResearch.WordTrace]
  refine ⟨19895472428808481266149909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13263648285872320844099939 19895472428808481266149909)
  ·
    refine ⟨932600270100397559350777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19895472428808481266149909 932600270100397559350777)
    ·
      refine ⟨699450202575298169513083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 932600270100397559350777 699450202575298169513083)
      ·
        refine ⟨1049175303862947254269625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699450202575298169513083 1049175303862947254269625)
        ·
          refine ⟨786881477897210440702219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1049175303862947254269625 786881477897210440702219)
          ·
            refine ⟨1180322216845815661053329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786881477897210440702219 1180322216845815661053329)
            ·
              refine ⟨885241662634361745789997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180322216845815661053329 885241662634361745789997)
              ·
                refine ⟨331965623487885654671249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 885241662634361745789997 331965623487885654671249)
                ·
                  refine ⟨248974217615914241003437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331965623487885654671249 248974217615914241003437)
                  ·
                    rfl

theorem cell20_545485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_545485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545485 prefixEnd_545485 := by exact prefixLift 545485
  have htrace : WordTrace (prefixWord ++ tailWord_545485) baseStart_545485 baseEnd_545485 := by
    simpa [prefixWord, tailWord_545485, baseEnd_545485] using wordTrace_append hprefix tailTrace_545485
  have hstable : (prefixWord ++ tailWord_545485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545485).length < 2 ^ (prefixWord ++ tailWord_545485).sum := by decide
  have hdescent : baseEnd_545485 < baseStart_545485 := by decide
  rcases family_descends (prefixWord ++ tailWord_545485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545503 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_545503 : Nat := 118140960795 + 545503 * 2 ^ 59
def prefixEnd_545503 : Nat := 4983230072969 + 3 ^ 40 * 545503 * 2
def baseEnd_545503 : Nat := 248982433306386178403363

theorem tailTrace_545503 : CollatzResearch.WordTrace tailWord_545503 prefixEnd_545503 248982433306386178403363 := by
  unfold tailWord_545503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896128942743270340305163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13264085961828846893536775 19896128942743270340305163)
  ·
    refine ⟨29844193414114905510457745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19896128942743270340305163 29844193414114905510457745)
    ·
      refine ⟨22383145060586179132843309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29844193414114905510457745 22383145060586179132843309)
      ·
        refine ⟨8393679397719817174816241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22383145060586179132843309 8393679397719817174816241)
        ·
          refine ⟨6295259548289862881112181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8393679397719817174816241 6295259548289862881112181)
          ·
            refine ⟨590180582652174645104267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6295259548289862881112181 590180582652174645104267)
            ·
              refine ⟨885270873978261967656401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590180582652174645104267 885270873978261967656401)
              ·
                refine ⟨663953155483696475742301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885270873978261967656401 663953155483696475742301)
                ·
                  refine ⟨248982433306386178403363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663953155483696475742301 248982433306386178403363)
                  ·
                    rfl

theorem cell20_545503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_545503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545503 prefixEnd_545503 := by exact prefixLift 545503
  have htrace : WordTrace (prefixWord ++ tailWord_545503) baseStart_545503 baseEnd_545503 := by
    simpa [prefixWord, tailWord_545503, baseEnd_545503] using wordTrace_append hprefix tailTrace_545503
  have hstable : (prefixWord ++ tailWord_545503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545503).length < 2 ^ (prefixWord ++ tailWord_545503).sum := by decide
  have hdescent : baseEnd_545503 < baseStart_545503 := by decide
  rcases family_descends (prefixWord ++ tailWord_545503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545534 : List Nat := [4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_545534 : Nat := 118140960795 + 545534 * 2 ^ 59
def prefixEnd_545534 : Nat := 4983230072969 + 3 ^ 40 * 545534 * 2
def baseEnd_545534 : Nat := 82998860850362616123301

theorem tailTrace_545534 : CollatzResearch.WordTrace tailWord_545534 prefixEnd_545534 82998860850362616123301 := by
  unfold tailWord_545534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487157450703870329335457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13264839737087308423122437 2487157450703870329335457)
  ·
    refine ⟨1865368088027902747001593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2487157450703870329335457 1865368088027902747001593)
    ·
      refine ⟨1399026066020927060251195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1865368088027902747001593 1399026066020927060251195)
      ·
        refine ⟨2098539099031390590376793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399026066020927060251195 2098539099031390590376793)
        ·
          refine ⟨1573904324273542942782595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2098539099031390590376793 1573904324273542942782595)
          ·
            refine ⟨2360856486410314414173893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573904324273542942782595 2360856486410314414173893)
            ·
              refine ⟨442660591201933952657605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2360856486410314414173893 442660591201933952657605)
              ·
                refine ⟨82998860850362616123301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442660591201933952657605 82998860850362616123301)
                ·
                  rfl

theorem cell20_545534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_545534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545534 prefixEnd_545534 := by exact prefixLift 545534
  have htrace : WordTrace (prefixWord ++ tailWord_545534) baseStart_545534 baseEnd_545534 := by
    simpa [prefixWord, tailWord_545534, baseEnd_545534] using wordTrace_append hprefix tailTrace_545534
  have hstable : (prefixWord ++ tailWord_545534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545534).length < 2 ^ (prefixWord ++ tailWord_545534).sum := by decide
  have hdescent : baseEnd_545534 < baseStart_545534 := by decide
  rcases family_descends (prefixWord ++ tailWord_545534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545545 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_545545 : Nat := 118140960795 + 545545 * 2 ^ 59
def prefixEnd_545545 : Nat := 4983230072969 + 3 ^ 40 * 545545 * 2
def baseEnd_545545 : Nat := 249001603250820699003191

theorem tailTrace_545545 : CollatzResearch.WordTrace tailWord_545545 prefixEnd_545545 249001603250820699003191 := by
  unfold tailWord_545545
  simp only [CollatzResearch.WordTrace]
  refine ⟨19897660808591111513334089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13265107205727407675556059 19897660808591111513334089)
  ·
    refine ⟨14923245606443333635000567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19897660808591111513334089 14923245606443333635000567)
    ·
      refine ⟨22384868409665000452500851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923245606443333635000567 22384868409665000452500851)
      ·
        refine ⟨33577302614497500678751277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22384868409665000452500851 33577302614497500678751277)
        ·
          refine ⟨12591488480436562754531729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33577302614497500678751277 12591488480436562754531729)
          ·
            refine ⟨9443616360327422065898797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12591488480436562754531729 9443616360327422065898797)
            ·
              refine ⟨3541356135122783274712049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9443616360327422065898797 3541356135122783274712049)
              ·
                refine ⟨2656017101342087456034037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541356135122783274712049 2656017101342087456034037)
                ·
                  refine ⟨249001603250820699003191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656017101342087456034037 249001603250820699003191)
                  ·
                    rfl

theorem cell20_545545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_545545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545545 prefixEnd_545545 := by exact prefixLift 545545
  have htrace : WordTrace (prefixWord ++ tailWord_545545) baseStart_545545 baseEnd_545545 := by
    simpa [prefixWord, tailWord_545545, baseEnd_545545] using wordTrace_append hprefix tailTrace_545545
  have hstable : (prefixWord ++ tailWord_545545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545545).length < 2 ^ (prefixWord ++ tailWord_545545).sum := by decide
  have hdescent : baseEnd_545545 < baseStart_545545 := by decide
  rcases family_descends (prefixWord ++ tailWord_545545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545562 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_545562 : Nat := 118140960795 + 545562 * 2 ^ 59
def prefixEnd_545562 : Nat := 4983230072969 + 3 ^ 40 * 545562 * 2
def baseEnd_545562 : Nat := 249009362514044195436455

theorem tailTrace_545562 : CollatzResearch.WordTrace tailWord_545562 prefixEnd_545562 249009362514044195436455 := by
  unfold tailWord_545562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974570212382380854175735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13265520566353015611135293 4974570212382380854175735)
  ·
    refine ⟨7461855318573571281263603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4974570212382380854175735 7461855318573571281263603)
    ·
      refine ⟨11192782977860356921895405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461855318573571281263603 11192782977860356921895405)
      ·
        refine ⟨4197293616697633845710777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11192782977860356921895405 4197293616697633845710777)
        ·
          refine ⟨3147970212523225384283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197293616697633845710777 3147970212523225384283083)
          ·
            refine ⟨4721955318784838076424625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147970212523225384283083 4721955318784838076424625)
            ·
              refine ⟨3541466489088628557318469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721955318784838076424625 3541466489088628557318469)
              ·
                refine ⟨664024966704117854497213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3541466489088628557318469 664024966704117854497213)
                ·
                  refine ⟨249009362514044195436455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664024966704117854497213 249009362514044195436455)
                  ·
                    rfl

theorem cell20_545562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_545562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545562 prefixEnd_545562 := by exact prefixLift 545562
  have htrace : WordTrace (prefixWord ++ tailWord_545562) baseStart_545562 baseEnd_545562 := by
    simpa [prefixWord, tailWord_545562, baseEnd_545562] using wordTrace_append hprefix tailTrace_545562
  have hstable : (prefixWord ++ tailWord_545562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545562).length < 2 ^ (prefixWord ++ tailWord_545562).sum := by decide
  have hdescent : baseEnd_545562 < baseStart_545562 := by decide
  rcases family_descends (prefixWord ++ tailWord_545562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545617 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_545617 : Nat := 118140960795 + 545617 * 2 ^ 59
def prefixEnd_545617 : Nat := 4983230072969 + 3 ^ 40 * 545617 * 2
def baseEnd_545617 : Nat := 249034466012708448602897

theorem tailTrace_545617 : CollatzResearch.WordTrace tailWord_545617 prefixEnd_545617 249034466012708448602897 := by
  unfold tailWord_545617
  simp only [CollatzResearch.WordTrace]
  refine ⟨19900286864330267809955105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13266857909553511873303403 19900286864330267809955105)
  ·
    refine ⟨14925215148247700857466329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19900286864330267809955105 14925215148247700857466329)
    ·
      refine ⟨11193911361185775643099747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14925215148247700857466329 11193911361185775643099747)
      ·
        refine ⟨16790867041778663464649621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193911361185775643099747 16790867041778663464649621)
        ·
          refine ⟨787071892583374849905451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16790867041778663464649621 787071892583374849905451)
          ·
            refine ⟨1180607838875062274858177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787071892583374849905451 1180607838875062274858177)
            ·
              refine ⟨885455879156296706143633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180607838875062274858177 885455879156296706143633)
              ·
                refine ⟨664091909367222529607725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885455879156296706143633 664091909367222529607725)
                ·
                  refine ⟨249034466012708448602897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664091909367222529607725 249034466012708448602897)
                  ·
                    rfl

theorem cell20_545617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_545617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545617 prefixEnd_545617 := by exact prefixLift 545617
  have htrace : WordTrace (prefixWord ++ tailWord_545617) baseStart_545617 baseEnd_545617 := by
    simpa [prefixWord, tailWord_545617, baseEnd_545617] using wordTrace_append hprefix tailTrace_545617
  have hstable : (prefixWord ++ tailWord_545617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545617).length < 2 ^ (prefixWord ++ tailWord_545617).sum := by decide
  have hdescent : baseEnd_545617 < baseStart_545617 := by decide
  rcases family_descends (prefixWord ++ tailWord_545617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545676 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_545676 : Nat := 118140960795 + 545676 * 2 ^ 59
def prefixEnd_545676 : Nat := 4983230072969 + 3 ^ 40 * 545676 * 2
def baseEnd_545676 : Nat := 249061395220366465635989

theorem tailTrace_545676 : CollatzResearch.WordTrace tailWord_545676 prefixEnd_545676 249061395220366465635989 := by
  unfold tailWord_545676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9951219385558260443176441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13268292514077680590901921 9951219385558260443176441)
  ·
    refine ⟨7463414539168695332382331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9951219385558260443176441 7463414539168695332382331)
    ·
      refine ⟨11195121808753042998573497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7463414539168695332382331 11195121808753042998573497)
      ·
        refine ⟨8396341356564782248930123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11195121808753042998573497 8396341356564782248930123)
        ·
          refine ⟨12594512034847173373395185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396341356564782248930123 12594512034847173373395185)
          ·
            refine ⟨9445884026135380030046389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594512034847173373395185 9445884026135380030046389)
            ·
              refine ⟨885551627450191877816849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9445884026135380030046389 885551627450191877816849)
              ·
                refine ⟨664163720587643908362637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885551627450191877816849 664163720587643908362637)
                ·
                  refine ⟨249061395220366465635989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664163720587643908362637 249061395220366465635989)
                  ·
                    rfl

theorem cell20_545676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_545676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545676 prefixEnd_545676 := by exact prefixLift 545676
  have htrace : WordTrace (prefixWord ++ tailWord_545676) baseStart_545676 baseEnd_545676 := by
    simpa [prefixWord, tailWord_545676, baseEnd_545676] using wordTrace_append hprefix tailTrace_545676
  have hstable : (prefixWord ++ tailWord_545676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545676).length < 2 ^ (prefixWord ++ tailWord_545676).sum := by decide
  have hdescent : baseEnd_545676 < baseStart_545676 := by decide
  rcases family_descends (prefixWord ++ tailWord_545676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545693 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_545693 : Nat := 118140960795 + 545693 * 2 ^ 59
def prefixEnd_545693 : Nat := 4983230072969 + 3 ^ 40 * 545693 * 2
def baseEnd_545693 : Nat := 249069154483589962069253

theorem tailTrace_545693 : CollatzResearch.WordTrace tailWord_545693 prefixEnd_545693 249069154483589962069253 := by
  unfold tailWord_545693
  simp only [CollatzResearch.WordTrace]
  refine ⟨19903058812054932789721733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13268705874703288526481155 19903058812054932789721733)
  ·
    refine ⟨3731823527260299898072825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19903058812054932789721733 3731823527260299898072825)
    ·
      refine ⟨2798867645445224923554619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3731823527260299898072825 2798867645445224923554619)
      ·
        refine ⟨4198301468167837385331929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798867645445224923554619 4198301468167837385331929)
        ·
          refine ⟨3148726101125878038998947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198301468167837385331929 3148726101125878038998947)
          ·
            refine ⟨4723089151688817058498421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148726101125878038998947 4723089151688817058498421)
            ·
              refine ⟨442789607970826599234227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4723089151688817058498421 442789607970826599234227)
              ·
                refine ⟨664184411956239898851341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442789607970826599234227 664184411956239898851341)
                ·
                  refine ⟨249069154483589962069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664184411956239898851341 249069154483589962069253)
                  ·
                    rfl

theorem cell20_545693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_545693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545693 prefixEnd_545693 := by exact prefixLift 545693
  have htrace : WordTrace (prefixWord ++ tailWord_545693) baseStart_545693 baseEnd_545693 := by
    simpa [prefixWord, tailWord_545693, baseEnd_545693] using wordTrace_append hprefix tailTrace_545693
  have hstable : (prefixWord ++ tailWord_545693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545693).length < 2 ^ (prefixWord ++ tailWord_545693).sum := by decide
  have hdescent : baseEnd_545693 < baseStart_545693 := by decide
  rcases family_descends (prefixWord ++ tailWord_545693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545703 : List Nat := [1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_545703 : Nat := 118140960795 + 545703 * 2 ^ 59
def prefixEnd_545703 : Nat := 4983230072969 + 3 ^ 40 * 545703 * 2
def baseEnd_545703 : Nat := 83024572918691457245293

theorem tailTrace_545703 : CollatzResearch.WordTrace tailWord_545703 prefixEnd_545703 83024572918691457245293 := by
  unfold tailWord_545703
  simp only [CollatzResearch.WordTrace]
  refine ⟨19903423542018704497585763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13268949028012469665057175 19903423542018704497585763)
  ·
    refine ⟨29855135313028056746378645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19903423542018704497585763 29855135313028056746378645)
    ·
      refine ⟨1399459467798190159986499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29855135313028056746378645 1399459467798190159986499)
      ·
        refine ⟨2099189201697285239979749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399459467798190159986499 2099189201697285239979749)
        ·
          refine ⟨393597975318240982496203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2099189201697285239979749 393597975318240982496203)
          ·
            refine ⟨590396962977361473744305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393597975318240982496203 590396962977361473744305)
            ·
              refine ⟨442797722233021105308229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590396962977361473744305 442797722233021105308229)
              ·
                refine ⟨83024572918691457245293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442797722233021105308229 83024572918691457245293)
                ·
                  rfl

theorem cell20_545703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_545703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545703 prefixEnd_545703 := by exact prefixLift 545703
  have htrace : WordTrace (prefixWord ++ tailWord_545703) baseStart_545703 baseEnd_545703 := by
    simpa [prefixWord, tailWord_545703, baseEnd_545703] using wordTrace_append hprefix tailTrace_545703
  have hstable : (prefixWord ++ tailWord_545703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545703).length < 2 ^ (prefixWord ++ tailWord_545703).sum := by decide
  have hdescent : baseEnd_545703 < baseStart_545703 := by decide
  rcases family_descends (prefixWord ++ tailWord_545703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545728 : List Nat := [2, 1, 1, 2, 3, 5, 6]
def baseStart_545728 : Nat := 118140960795 + 545728 * 2 ^ 59
def prefixEnd_545728 : Nat := 4983230072969 + 3 ^ 40 * 545728 * 2
def baseEnd_545728 : Nat := 27676125493031710655827

theorem tailTrace_545728 : CollatzResearch.WordTrace tailWord_545728 prefixEnd_545728 27676125493031710655827 := by
  unfold tailWord_545728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952167683464066883622919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13269556911285422511497225 9952167683464066883622919)
  ·
    refine ⟨14928251525196100325434379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9952167683464066883622919 14928251525196100325434379)
    ·
      refine ⟨22392377287794150488151569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14928251525196100325434379 22392377287794150488151569)
      ·
        refine ⟨16794282965845612866113677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22392377287794150488151569 16794282965845612866113677)
        ·
          refine ⟨6297856112192104824792629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16794282965845612866113677 6297856112192104824792629)
          ·
            refine ⟨590424010518009827324309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6297856112192104824792629 590424010518009827324309)
            ·
              refine ⟨27676125493031710655827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 590424010518009827324309 27676125493031710655827)
              ·
                rfl

theorem cell20_545728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_545728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545728 prefixEnd_545728 := by exact prefixLift 545728
  have htrace : WordTrace (prefixWord ++ tailWord_545728) baseStart_545728 baseEnd_545728 := by
    simpa [prefixWord, tailWord_545728, baseEnd_545728] using wordTrace_append hprefix tailTrace_545728
  have hstable : (prefixWord ++ tailWord_545728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545728).length < 2 ^ (prefixWord ++ tailWord_545728).sum := by decide
  have hdescent : baseEnd_545728 < baseStart_545728 := by decide
  rcases family_descends (prefixWord ++ tailWord_545728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545735 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_545735 : Nat := 118140960795 + 545735 * 2 ^ 59
def prefixEnd_545735 : Nat := 4983230072969 + 3 ^ 40 * 545735 * 2
def baseEnd_545735 : Nat := 249088324428024482669081

theorem tailTrace_545735 : CollatzResearch.WordTrace tailWord_545735 prefixEnd_545735 249088324428024482669081 := by
  unfold tailWord_545735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19904590677902773962750659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13269727118601849308500439 19904590677902773962750659)
  ·
    refine ⟨29856886016854160944125989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19904590677902773962750659 29856886016854160944125989)
    ·
      refine ⟨5598166128160155177023623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29856886016854160944125989 5598166128160155177023623)
      ·
        refine ⟨8397249192240232765535435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598166128160155177023623 8397249192240232765535435)
        ·
          refine ⟨12595873788360349148303153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8397249192240232765535435 12595873788360349148303153)
          ·
            refine ⟨9446905341270261861227365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12595873788360349148303153 9446905341270261861227365)
            ·
              refine ⟨1771294751488174098980131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9446905341270261861227365 1771294751488174098980131)
              ·
                refine ⟨2656942127232261148470197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771294751488174098980131 2656942127232261148470197)
                ·
                  refine ⟨249088324428024482669081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656942127232261148470197 249088324428024482669081)
                  ·
                    rfl

theorem cell20_545735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_545735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545735 prefixEnd_545735 := by exact prefixLift 545735
  have htrace : WordTrace (prefixWord ++ tailWord_545735) baseStart_545735 baseEnd_545735 := by
    simpa [prefixWord, tailWord_545735, baseEnd_545735] using wordTrace_append hprefix tailTrace_545735
  have hstable : (prefixWord ++ tailWord_545735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545735).length < 2 ^ (prefixWord ++ tailWord_545735).sum := by decide
  have hdescent : baseEnd_545735 < baseStart_545735 := by decide
  rcases family_descends (prefixWord ++ tailWord_545735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545748 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_545748 : Nat := 118140960795 + 545748 * 2 ^ 59
def prefixEnd_545748 : Nat := 4983230072969 + 3 ^ 40 * 545748 * 2
def baseEnd_545748 : Nat := 249094257982254215235695

theorem tailTrace_545748 : CollatzResearch.WordTrace tailWord_545748 prefixEnd_545748 249094257982254215235695 := by
  unfold tailWord_545748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952532413427838591486949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13270043217903784788649265 9952532413427838591486949)
  ·
    refine ⟨1866099827517719735903803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9952532413427838591486949 1866099827517719735903803)
    ·
      refine ⟨2799149741276579603855705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866099827517719735903803 2799149741276579603855705)
      ·
        refine ⟨2099362305957434702891779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799149741276579603855705 2099362305957434702891779)
        ·
          refine ⟨3149043458936152054337669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099362305957434702891779 3149043458936152054337669)
          ·
            refine ⟨590445648550528510188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3149043458936152054337669 590445648550528510188313)
            ·
              refine ⟨442834236412896382641235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590445648550528510188313 442834236412896382641235)
              ·
                refine ⟨664251354619344573961853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442834236412896382641235 664251354619344573961853)
                ·
                  refine ⟨249094257982254215235695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664251354619344573961853 249094257982254215235695)
                  ·
                    rfl

theorem cell20_545748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_545748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545748 prefixEnd_545748 := by exact prefixLift 545748
  have htrace : WordTrace (prefixWord ++ tailWord_545748) baseStart_545748 baseEnd_545748 := by
    simpa [prefixWord, tailWord_545748, baseEnd_545748] using wordTrace_append hprefix tailTrace_545748
  have hstable : (prefixWord ++ tailWord_545748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545748).length < 2 ^ (prefixWord ++ tailWord_545748).sum := by decide
  have hdescent : baseEnd_545748 < baseStart_545748 := by decide
  rcases family_descends (prefixWord ++ tailWord_545748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545752 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_545752 : Nat := 118140960795 + 545752 * 2 ^ 59
def prefixEnd_545752 : Nat := 4983230072969 + 3 ^ 40 * 545752 * 2
def baseEnd_545752 : Nat := 249096083691247979102345

theorem tailTrace_545752 : CollatzResearch.WordTrace tailWord_545752 prefixEnd_545752 249096083691247979102345 := by
  unfold tailWord_545752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952605359420592933059755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13270140479227457244079673 9952605359420592933059755)
  ·
    refine ⟨14928908039130889399589633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9952605359420592933059755 14928908039130889399589633)
    ·
      refine ⟨11196681029348167049692225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14928908039130889399589633 11196681029348167049692225)
      ·
        refine ⟨8397510772011125287269169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11196681029348167049692225 8397510772011125287269169)
        ·
          refine ⟨6298133079008343965451877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8397510772011125287269169 6298133079008343965451877)
          ·
            refine ⟨1180899952314064493522227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6298133079008343965451877 1180899952314064493522227)
            ·
              refine ⟨1771349928471096740283341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180899952314064493522227 1771349928471096740283341)
              ·
                refine ⟨664256223176661277606253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1771349928471096740283341 664256223176661277606253)
                ·
                  refine ⟨249096083691247979102345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664256223176661277606253 249096083691247979102345)
                  ·
                    rfl

theorem cell20_545752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_545752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545752 prefixEnd_545752 := by exact prefixLift 545752
  have htrace : WordTrace (prefixWord ++ tailWord_545752) baseStart_545752 baseEnd_545752 := by
    simpa [prefixWord, tailWord_545752, baseEnd_545752] using wordTrace_append hprefix tailTrace_545752
  have hstable : (prefixWord ++ tailWord_545752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545752).length < 2 ^ (prefixWord ++ tailWord_545752).sum := by decide
  have hdescent : baseEnd_545752 < baseStart_545752 := by decide
  rcases family_descends (prefixWord ++ tailWord_545752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545793 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 2]
def baseStart_545793 : Nat := 118140960795 + 545793 * 2 ^ 59
def prefixEnd_545793 : Nat := 4983230072969 + 3 ^ 40 * 545793 * 2
def baseEnd_545793 : Nat := 249114797208434058735511

theorem tailTrace_545793 : CollatzResearch.WordTrace tailWord_545793 prefixEnd_545793 249114797208434058735511 := by
  unfold tailWord_545793
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906706111692649868362033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13271137407795099912241355 19906706111692649868362033)
  ·
    refine ⟨14930029583769487401271525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19906706111692649868362033 14930029583769487401271525)
    ·
      refine ⟨2799380546956778887738411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14930029583769487401271525 2799380546956778887738411)
      ·
        refine ⟨4199070820435168331607617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799380546956778887738411 4199070820435168331607617)
        ·
          refine ⟨3149303115326376248705713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199070820435168331607617 3149303115326376248705713)
          ·
            refine ⟨2361977336494782186529285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149303115326376248705713 2361977336494782186529285)
            ·
              refine ⟨442870750592771659974241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2361977336494782186529285 442870750592771659974241)
              ·
                refine ⟨332153062944578744980681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442870750592771659974241 332153062944578744980681)
                ·
                  refine ⟨249114797208434058735511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332153062944578744980681 249114797208434058735511)
                  ·
                    rfl

theorem cell20_545793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_545793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545793 prefixEnd_545793 := by exact prefixLift 545793
  have htrace : WordTrace (prefixWord ++ tailWord_545793) baseStart_545793 baseEnd_545793 := by
    simpa [prefixWord, tailWord_545793, baseEnd_545793] using wordTrace_append hprefix tailTrace_545793
  have hstable : (prefixWord ++ tailWord_545793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545793).length < 2 ^ (prefixWord ++ tailWord_545793).sum := by decide
  have hdescent : baseEnd_545793 < baseStart_545793 := by decide
  rcases family_descends (prefixWord ++ tailWord_545793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545804 : List Nat := [2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_545804 : Nat := 118140960795 + 545804 * 2 ^ 59
def prefixEnd_545804 : Nat := 4983230072969 + 3 ^ 40 * 545804 * 2
def baseEnd_545804 : Nat := 83039939302722303122933

theorem tailTrace_545804 : CollatzResearch.WordTrace tailWord_545804 prefixEnd_545804 83039939302722303122933 := by
  unfold tailWord_545804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953553657326399373506233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13271404876435199164674977 9953553657326399373506233)
  ·
    refine ⟨7465165242994799530129675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9953553657326399373506233 7465165242994799530129675)
    ·
      refine ⟨11197747864492199295194513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465165242994799530129675 11197747864492199295194513)
      ·
        refine ⟨8398310898369149471395885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11197747864492199295194513 8398310898369149471395885)
        ·
          refine ⟨3149366586888431051773457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8398310898369149471395885 3149366586888431051773457)
          ·
            refine ⟨2362024940166323288830093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149366586888431051773457 2362024940166323288830093)
            ·
              refine ⟨885759352562371233311285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2362024940166323288830093 885759352562371233311285)
              ·
                refine ⟨83039939302722303122933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 885759352562371233311285 83039939302722303122933)
                ·
                  rfl

theorem cell20_545804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_545804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545804 prefixEnd_545804 := by exact prefixLift 545804
  have htrace : WordTrace (prefixWord ++ tailWord_545804) baseStart_545804 baseEnd_545804 := by
    simpa [prefixWord, tailWord_545804, baseEnd_545804] using wordTrace_append hprefix tailTrace_545804
  have hstable : (prefixWord ++ tailWord_545804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545804).length < 2 ^ (prefixWord ++ tailWord_545804).sum := by decide
  have hdescent : baseEnd_545804 < baseStart_545804 := by decide
  rcases family_descends (prefixWord ++ tailWord_545804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545810 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_545810 : Nat := 118140960795 + 545810 * 2 ^ 59
def prefixEnd_545810 : Nat := 4983230072969 + 3 ^ 40 * 545810 * 2
def baseEnd_545810 : Nat := 249122556471657555168775

theorem tailTrace_545810 : CollatzResearch.WordTrace tailWord_545810 prefixEnd_545810 249122556471657555168775 := by
  unfold tailWord_545810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976831538157765442932721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13271550768420707847820589 4976831538157765442932721)
  ·
    refine ⟨3732623653618324082199541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976831538157765442932721 3732623653618324082199541)
    ·
      refine ⟨349933467526717882706207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3732623653618324082199541 349933467526717882706207)
      ·
        refine ⟨524900201290076824059311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349933467526717882706207 524900201290076824059311)
        ·
          refine ⟨787350301935115236088967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524900201290076824059311 787350301935115236088967)
          ·
            refine ⟨1181025452902672854133451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787350301935115236088967 1181025452902672854133451)
            ·
              refine ⟨1771538179354009281200177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181025452902672854133451 1771538179354009281200177)
              ·
                refine ⟨1328653634515506960900133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771538179354009281200177 1328653634515506960900133)
                ·
                  refine ⟨249122556471657555168775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328653634515506960900133 249122556471657555168775)
                  ·
                    rfl

theorem cell20_545810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_545810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545810 prefixEnd_545810 := by exact prefixLift 545810
  have htrace : WordTrace (prefixWord ++ tailWord_545810) baseStart_545810 baseEnd_545810 := by
    simpa [prefixWord, tailWord_545810, baseEnd_545810] using wordTrace_append hprefix tailTrace_545810
  have hstable : (prefixWord ++ tailWord_545810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545810).length < 2 ^ (prefixWord ++ tailWord_545810).sum := by decide
  have hdescent : baseEnd_545810 < baseStart_545810 := by decide
  rcases family_descends (prefixWord ++ tailWord_545810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545831 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 2]
def baseStart_545831 : Nat := 118140960795 + 545831 * 2 ^ 59
def prefixEnd_545831 : Nat := 4983230072969 + 3 ^ 40 * 545831 * 2
def baseEnd_545831 : Nat := 249132141443874815468689

theorem tailTrace_545831 : CollatzResearch.WordTrace tailWord_545831 prefixEnd_545831 249132141443874815468689 := by
  unfold tailWord_545831
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908092085554982358245347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13272061390369988238830231 19908092085554982358245347)
  ·
    refine ⟨29862138128332473537368021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19908092085554982358245347 29862138128332473537368021)
    ·
      refine ⟨699893862382792348532063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29862138128332473537368021 699893862382792348532063)
      ·
        refine ⟨1049840793574188522798095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699893862382792348532063 1049840793574188522798095)
        ·
          refine ⟨1574761190361282784197143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049840793574188522798095 1574761190361282784197143)
          ·
            refine ⟨2362141785541924176295715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574761190361282784197143 2362141785541924176295715)
            ·
              refine ⟨3543212678312886264443573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362141785541924176295715 3543212678312886264443573)
              ·
                refine ⟨332176188591833087291585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3543212678312886264443573 332176188591833087291585)
                ·
                  refine ⟨249132141443874815468689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332176188591833087291585 249132141443874815468689)
                  ·
                    rfl

theorem cell20_545831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2].length) (baseStart_545831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545831 prefixEnd_545831 := by exact prefixLift 545831
  have htrace : WordTrace (prefixWord ++ tailWord_545831) baseStart_545831 baseEnd_545831 := by
    simpa [prefixWord, tailWord_545831, baseEnd_545831] using wordTrace_append hprefix tailTrace_545831
  have hstable : (prefixWord ++ tailWord_545831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545831).length < 2 ^ (prefixWord ++ tailWord_545831).sum := by decide
  have hdescent : baseEnd_545831 < baseStart_545831 := by decide
  rcases family_descends (prefixWord ++ tailWord_545831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545852 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_545852 : Nat := 118140960795 + 545852 * 2 ^ 59
def prefixEnd_545852 : Nat := 4983230072969 + 3 ^ 40 * 545852 * 2
def baseEnd_545852 : Nat := 249141726416092075768603

theorem tailTrace_545852 : CollatzResearch.WordTrace tailWord_545852 prefixEnd_545852 249141726416092075768603 := by
  unfold tailWord_545852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954429009239451472379905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13272572012319268629839873 9954429009239451472379905)
  ·
    refine ⟨7465821756929588604284929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9954429009239451472379905 7465821756929588604284929)
    ·
      refine ⟨5599366317697191453213697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7465821756929588604284929 5599366317697191453213697)
      ·
        refine ⟨4199524738272893589910273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5599366317697191453213697 4199524738272893589910273)
        ·
          refine ⟨3149643553704670192432705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199524738272893589910273 3149643553704670192432705)
          ·
            refine ⟨2362232665278502644324529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149643553704670192432705 2362232665278502644324529)
            ·
              refine ⟨1771674498958876983243397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362232665278502644324529 1771674498958876983243397)
              ·
                refine ⟨332188968554789434358137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1771674498958876983243397 332188968554789434358137)
                ·
                  refine ⟨249141726416092075768603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332188968554789434358137 249141726416092075768603)
                  ·
                    rfl

theorem cell20_545852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_545852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545852 prefixEnd_545852 := by exact prefixLift 545852
  have htrace : WordTrace (prefixWord ++ tailWord_545852) baseStart_545852 baseEnd_545852 := by
    simpa [prefixWord, tailWord_545852, baseEnd_545852] using wordTrace_append hprefix tailTrace_545852
  have hstable : (prefixWord ++ tailWord_545852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545852).length < 2 ^ (prefixWord ++ tailWord_545852).sum := by decide
  have hdescent : baseEnd_545852 < baseStart_545852 := by decide
  rcases family_descends (prefixWord ++ tailWord_545852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545921 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_545921 : Nat := 118140960795 + 545921 * 2 ^ 59
def prefixEnd_545921 : Nat := 4983230072969 + 3 ^ 40 * 545921 * 2
def baseEnd_545921 : Nat := 249173219896234502468321

theorem tailTrace_545921 : CollatzResearch.WordTrace tailWord_545921 prefixEnd_545921 249173219896234502468321 := by
  unfold tailWord_545921
  simp only [CollatzResearch.WordTrace]
  refine ⟨19911374655228927729021617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13274249770152618486014411 19911374655228927729021617)
  ·
    refine ⟨14933530991421695796766213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19911374655228927729021617 14933530991421695796766213)
    ·
      refine ⟨2800037060891567961893665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14933530991421695796766213 2800037060891567961893665)
      ·
        refine ⟨2100027795668675971420249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800037060891567961893665 2100027795668675971420249)
        ·
          refine ⟨1575020846751506978565187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100027795668675971420249 1575020846751506978565187)
          ·
            refine ⟨2362531270127260467847781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575020846751506978565187 2362531270127260467847781)
            ·
              refine ⟨442974613148861337721459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2362531270127260467847781 442974613148861337721459)
              ·
                refine ⟨664461919723292006582189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442974613148861337721459 664461919723292006582189)
                ·
                  refine ⟨249173219896234502468321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664461919723292006582189 249173219896234502468321)
                  ·
                    rfl

theorem cell20_545921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_545921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545921 prefixEnd_545921 := by exact prefixLift 545921
  have htrace : WordTrace (prefixWord ++ tailWord_545921) baseStart_545921 baseEnd_545921 := by
    simpa [prefixWord, tailWord_545921, baseEnd_545921] using wordTrace_append hprefix tailTrace_545921
  have hstable : (prefixWord ++ tailWord_545921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545921).length < 2 ^ (prefixWord ++ tailWord_545921).sum := by decide
  have hdescent : baseEnd_545921 < baseStart_545921 := by decide
  rcases family_descends (prefixWord ++ tailWord_545921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_545932 : Nat := 118140960795 + 545932 * 2 ^ 59
def prefixEnd_545932 : Nat := 4983230072969 + 3 ^ 40 * 545932 * 2
def baseEnd_545932 : Nat := 249178240595967353101609

theorem tailTrace_545932 : CollatzResearch.WordTrace tailWord_545932 prefixEnd_545932 249178240595967353101609 := by
  unfold tailWord_545932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955887929094538303836025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13274517238792717738448033 9955887929094538303836025)
  ·
    refine ⟨7466915946820903727877019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9955887929094538303836025 7466915946820903727877019)
    ·
      refine ⟨11200373920231355591815529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7466915946820903727877019 11200373920231355591815529)
      ·
        refine ⟨8400280440173516693861647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11200373920231355591815529 8400280440173516693861647)
        ·
          refine ⟨12600420660260275040792471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8400280440173516693861647 12600420660260275040792471)
          ·
            refine ⟨18900630990390412561188707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12600420660260275040792471 18900630990390412561188707)
            ·
              refine ⟨28350946485585618841783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18900630990390412561188707 28350946485585618841783061)
              ·
                refine ⟨1328950616511825883208581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28350946485585618841783061 1328950616511825883208581)
                ·
                  refine ⟨249178240595967353101609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328950616511825883208581 249178240595967353101609)
                  ·
                    rfl

theorem cell20_545932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_545932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545932 prefixEnd_545932 := by exact prefixLift 545932
  have htrace : WordTrace (prefixWord ++ tailWord_545932) baseStart_545932 baseEnd_545932 := by
    simpa [prefixWord, tailWord_545932, baseEnd_545932] using wordTrace_append hprefix tailTrace_545932
  have hstable : (prefixWord ++ tailWord_545932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545932).length < 2 ^ (prefixWord ++ tailWord_545932).sum := by decide
  have hdescent : baseEnd_545932 < baseStart_545932 := by decide
  rcases family_descends (prefixWord ++ tailWord_545932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545939 : List Nat := [1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_545939 : Nat := 118140960795 + 545939 * 2 ^ 59
def prefixEnd_545939 : Nat := 4983230072969 + 3 ^ 40 * 545939 * 2
def baseEnd_545939 : Nat := 83060478528902146622749

theorem tailTrace_545939 : CollatzResearch.WordTrace tailWord_545939 prefixEnd_545939 83060478528902146622749 := by
  unfold tailWord_545939
  simp only [CollatzResearch.WordTrace]
  refine ⟨19912031169163716803176871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13274687446109144535451247 19912031169163716803176871)
  ·
    refine ⟨29868046753745575204765307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19912031169163716803176871 29868046753745575204765307)
    ·
      refine ⟨44802070130618362807147961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29868046753745575204765307 44802070130618362807147961)
      ·
        refine ⟨33601552597963772105360971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44802070130618362807147961 33601552597963772105360971)
        ·
          refine ⟨50402328896945658158041457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33601552597963772105360971 50402328896945658158041457)
          ·
            refine ⟨37801746672709243618531093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50402328896945658158041457 37801746672709243618531093)
            ·
              refine ⟨1771956875283245794618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37801746672709243618531093 1771956875283245794618645)
              ·
                refine ⟨83060478528902146622749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771956875283245794618645 83060478528902146622749)
                ·
                  rfl

theorem cell20_545939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_545939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545939 prefixEnd_545939 := by exact prefixLift 545939
  have htrace : WordTrace (prefixWord ++ tailWord_545939) baseStart_545939 baseEnd_545939 := by
    simpa [prefixWord, tailWord_545939, baseEnd_545939] using wordTrace_append hprefix tailTrace_545939
  have hstable : (prefixWord ++ tailWord_545939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545939).length < 2 ^ (prefixWord ++ tailWord_545939).sum := by decide
  have hdescent : baseEnd_545939 < baseStart_545939 := by decide
  rcases family_descends (prefixWord ++ tailWord_545939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545959 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_545959 : Nat := 118140960795 + 545959 * 2 ^ 59
def prefixEnd_545959 : Nat := 4983230072969 + 3 ^ 40 * 545959 * 2
def baseEnd_545959 : Nat := 249190564131675259201499

theorem tailTrace_545959 : CollatzResearch.WordTrace tailWord_545959 prefixEnd_545959 249190564131675259201499 := by
  unfold tailWord_545959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19912760629091260218904931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13275173752727506812603287 19912760629091260218904931)
  ·
    refine ⟨29869140943636890328357397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19912760629091260218904931 29869140943636890328357397)
    ·
      refine ⟨1400115981732979234141753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29869140943636890328357397 1400115981732979234141753)
      ·
        refine ⟨1050086986299734425606315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400115981732979234141753 1050086986299734425606315)
        ·
          refine ⟨1575130479449601638409473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050086986299734425606315 1575130479449601638409473)
          ·
            refine ⟨1181347859587201228807105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575130479449601638409473 1181347859587201228807105)
            ·
              refine ⟨886010894690400921605329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181347859587201228807105 886010894690400921605329)
              ·
                refine ⟨664508171017800691203997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886010894690400921605329 664508171017800691203997)
                ·
                  refine ⟨249190564131675259201499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664508171017800691203997 249190564131675259201499)
                  ·
                    rfl

theorem cell20_545959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_545959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545959 prefixEnd_545959 := by exact prefixLift 545959
  have htrace : WordTrace (prefixWord ++ tailWord_545959) baseStart_545959 baseEnd_545959 := by
    simpa [prefixWord, tailWord_545959, baseEnd_545959] using wordTrace_append hprefix tailTrace_545959
  have hstable : (prefixWord ++ tailWord_545959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545959).length < 2 ^ (prefixWord ++ tailWord_545959).sum := by decide
  have hdescent : baseEnd_545959 < baseStart_545959 := by decide
  rcases family_descends (prefixWord ++ tailWord_545959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545962 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_545962 : Nat := 118140960795 + 545962 * 2 ^ 59
def prefixEnd_545962 : Nat := 4983230072969 + 3 ^ 40 * 545962 * 2
def baseEnd_545962 : Nat := 249191933413420582101487

theorem tailTrace_545962 : CollatzResearch.WordTrace tailWord_545962 prefixEnd_545962 249191933413420582101487 := by
  unfold tailWord_545962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978217512020097932816035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13275246698720261154176093 4978217512020097932816035)
  ·
    refine ⟨7467326268030146899224053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4978217512020097932816035 7467326268030146899224053)
    ·
      refine ⟨700061837627826271802255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7467326268030146899224053 700061837627826271802255)
      ·
        refine ⟨1050092756441739407703383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700061837627826271802255 1050092756441739407703383)
        ·
          refine ⟨1575139134662609111555075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050092756441739407703383 1575139134662609111555075)
          ·
            refine ⟨2362708701993913667332613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575139134662609111555075 2362708701993913667332613)
            ·
              refine ⟨443007881623858812624865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2362708701993913667332613 443007881623858812624865)
              ·
                refine ⟨332255911217894109468649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443007881623858812624865 332255911217894109468649)
                ·
                  refine ⟨249191933413420582101487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332255911217894109468649 249191933413420582101487)
                  ·
                    rfl

theorem cell20_545962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_545962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545962 prefixEnd_545962 := by exact prefixLift 545962
  have htrace : WordTrace (prefixWord ++ tailWord_545962) baseStart_545962 baseEnd_545962 := by
    simpa [prefixWord, tailWord_545962, baseEnd_545962] using wordTrace_append hprefix tailTrace_545962
  have hstable : (prefixWord ++ tailWord_545962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545962).length < 2 ^ (prefixWord ++ tailWord_545962).sum := by decide
  have hdescent : baseEnd_545962 < baseStart_545962 := by decide
  rcases family_descends (prefixWord ++ tailWord_545962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545980 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_545980 : Nat := 118140960795 + 545980 * 2 ^ 59
def prefixEnd_545980 : Nat := 4983230072969 + 3 ^ 40 * 545980 * 2
def baseEnd_545980 : Nat := 249200149103892519501413

theorem tailTrace_545980 : CollatzResearch.WordTrace tailWord_545980 prefixEnd_545980 249200149103892519501413 := by
  unfold tailWord_545980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956763281007590402709697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13275684374676787203612929 9956763281007590402709697)
  ·
    refine ⟨7467572460755692802032273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9956763281007590402709697 7467572460755692802032273)
    ·
      refine ⟨5600679345566769601524205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7467572460755692802032273 5600679345566769601524205)
      ·
        refine ⟨2100254754587538600571577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5600679345566769601524205 2100254754587538600571577)
        ·
          refine ⟨1575191065940653950428683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100254754587538600571577 1575191065940653950428683)
          ·
            refine ⟨2362786598910980925643025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575191065940653950428683 2362786598910980925643025)
            ·
              refine ⟨1772089949183235694232269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362786598910980925643025 1772089949183235694232269)
              ·
                refine ⟨664533730943713385337101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1772089949183235694232269 664533730943713385337101)
                ·
                  refine ⟨249200149103892519501413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664533730943713385337101 249200149103892519501413)
                  ·
                    rfl

theorem cell20_545980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_545980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_545980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_545980 prefixEnd_545980 := by exact prefixLift 545980
  have htrace : WordTrace (prefixWord ++ tailWord_545980) baseStart_545980 baseEnd_545980 := by
    simpa [prefixWord, tailWord_545980, baseEnd_545980] using wordTrace_append hprefix tailTrace_545980
  have hstable : (prefixWord ++ tailWord_545980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545980).length < 2 ^ (prefixWord ++ tailWord_545980).sum := by decide
  have hdescent : baseEnd_545980 < baseStart_545980 := by decide
  rcases family_descends (prefixWord ++ tailWord_545980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546049 : List Nat := [1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_546049 : Nat := 118140960795 + 546049 * 2 ^ 59
def prefixEnd_546049 : Nat := 4983230072969 + 3 ^ 40 * 546049 * 2
def baseEnd_546049 : Nat := 83077214194678315400377

theorem tailTrace_546049 : CollatzResearch.WordTrace tailWord_546049 prefixEnd_546049 83077214194678315400377 := by
  unfold tailWord_546049
  simp only [CollatzResearch.WordTrace]
  refine ⟨19916043198765205589681201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13277362132510137059787467 19916043198765205589681201)
  ·
    refine ⟨14937032399073904192260901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19916043198765205589681201 14937032399073904192260901)
    ·
      refine ⟨2800693574826357036048919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14937032399073904192260901 2800693574826357036048919)
      ·
        refine ⟨4201040362239535554073379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800693574826357036048919 4201040362239535554073379)
        ·
          refine ⟨6301560543359303331110069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201040362239535554073379 6301560543359303331110069)
          ·
            refine ⟨590771300939934687291569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6301560543359303331110069 590771300939934687291569)
            ·
              refine ⟨443078475704951015468677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590771300939934687291569 443078475704951015468677)
              ·
                refine ⟨83077214194678315400377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443078475704951015468677 83077214194678315400377)
                ·
                  rfl

theorem cell20_546049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_546049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546049 prefixEnd_546049 := by exact prefixLift 546049
  have htrace : WordTrace (prefixWord ++ tailWord_546049) baseStart_546049 baseEnd_546049 := by
    simpa [prefixWord, tailWord_546049, baseEnd_546049] using wordTrace_append hprefix tailTrace_546049
  have hstable : (prefixWord ++ tailWord_546049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546049).length < 2 ^ (prefixWord ++ tailWord_546049).sum := by decide
  have hdescent : baseEnd_546049 < baseStart_546049 := by decide
  rcases family_descends (prefixWord ++ tailWord_546049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546053 : List Nat := [1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_546053 : Nat := 118140960795 + 546053 * 2 ^ 59
def prefixEnd_546053 : Nat := 4983230072969 + 3 ^ 40 * 546053 * 2
def baseEnd_546053 : Nat := 83077822764342903355927

theorem tailTrace_546053 : CollatzResearch.WordTrace tailWord_546053 prefixEnd_546053 83077822764342903355927 := by
  unfold tailWord_546053
  simp only [CollatzResearch.WordTrace]
  refine ⟨19916189090750714272826813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13277459393833809515217875 19916189090750714272826813)
  ·
    refine ⟨7468570909031517852310055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19916189090750714272826813 7468570909031517852310055)
    ·
      refine ⟨11202856363547276778465083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468570909031517852310055 11202856363547276778465083)
      ·
        refine ⟨16804284545320915167697625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11202856363547276778465083 16804284545320915167697625)
        ·
          refine ⟨12603213408990686375773219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16804284545320915167697625 12603213408990686375773219)
          ·
            refine ⟨18904820113486029563659829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12603213408990686375773219 18904820113486029563659829)
            ·
              refine ⟨1772326885639315271593109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18904820113486029563659829 1772326885639315271593109)
              ·
                refine ⟨83077822764342903355927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1772326885639315271593109 83077822764342903355927)
                ·
                  rfl

theorem cell20_546053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_546053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546053 prefixEnd_546053 := by exact prefixLift 546053
  have htrace : WordTrace (prefixWord ++ tailWord_546053) baseStart_546053 baseEnd_546053 := by
    simpa [prefixWord, tailWord_546053, baseEnd_546053] using wordTrace_append hprefix tailTrace_546053
  have hstable : (prefixWord ++ tailWord_546053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546053).length < 2 ^ (prefixWord ++ tailWord_546053).sum := by decide
  have hdescent : baseEnd_546053 < baseStart_546053 := by decide
  rcases family_descends (prefixWord ++ tailWord_546053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546066 : List Nat := [3, 2, 4, 2, 1, 2, 6]
def baseStart_546066 : Nat := 118140960795 + 546066 * 2 ^ 59
def prefixEnd_546066 : Nat := 4983230072969 + 3 ^ 40 * 546066 * 2
def baseEnd_546066 : Nat := 27693266871917604737155

theorem tailTrace_546066 : CollatzResearch.WordTrace tailWord_546066 prefixEnd_546066 27693266871917604737155 := by
  unfold tailWord_546066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979165809925904373262513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13277775493135744995366701 4979165809925904373262513)
  ·
    refine ⟨3734374357444428279946885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4979165809925904373262513 3734374357444428279946885)
    ·
      refine ⟨700195192020830302490041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3734374357444428279946885 700195192020830302490041)
      ·
        refine ⟨525146394015622726867531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700195192020830302490041 525146394015622726867531)
        ·
          refine ⟨787719591023434090301297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525146394015622726867531 787719591023434090301297)
          ·
            refine ⟨590789693267575567725973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787719591023434090301297 590789693267575567725973)
            ·
              refine ⟨27693266871917604737155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 590789693267575567725973 27693266871917604737155)
              ·
                rfl

theorem cell20_546066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_546066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546066 prefixEnd_546066 := by exact prefixLift 546066
  have htrace : WordTrace (prefixWord ++ tailWord_546066) baseStart_546066 baseEnd_546066 := by
    simpa [prefixWord, tailWord_546066, baseEnd_546066] using wordTrace_append hprefix tailTrace_546066
  have hstable : (prefixWord ++ tailWord_546066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546066).length < 2 ^ (prefixWord ++ tailWord_546066).sum := by decide
  have hdescent : baseEnd_546066 < baseStart_546066 := by decide
  rcases family_descends (prefixWord ++ tailWord_546066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546080 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_546080 : Nat := 118140960795 + 546080 * 2 ^ 59
def prefixEnd_546080 : Nat := 4983230072969 + 3 ^ 40 * 546080 * 2
def baseEnd_546080 : Nat := 249245791828736616167671

theorem tailTrace_546080 : CollatzResearch.WordTrace tailWord_546080 prefixEnd_546080 249245791828736616167671 := by
  unfold tailWord_546080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958586930826448942029847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13278115907768598589373129 9958586930826448942029847)
  ·
    refine ⟨14937880396239673413044771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9958586930826448942029847 14937880396239673413044771)
    ·
      refine ⟨22406820594359510119567157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14937880396239673413044771 22406820594359510119567157)
      ·
        refine ⟨2100639430721204073709421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22406820594359510119567157 2100639430721204073709421)
        ·
          refine ⟨787739786520451527641033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2100639430721204073709421 787739786520451527641033)
          ·
            refine ⟨590804839890338645730775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787739786520451527641033 590804839890338645730775)
            ·
              refine ⟨886207259835507968596163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590804839890338645730775 886207259835507968596163)
              ·
                refine ⟨1329310889753261952894245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886207259835507968596163 1329310889753261952894245)
                ·
                  refine ⟨249245791828736616167671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329310889753261952894245 249245791828736616167671)
                  ·
                    rfl

theorem cell20_546080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_546080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546080 prefixEnd_546080 := by exact prefixLift 546080
  have htrace : WordTrace (prefixWord ++ tailWord_546080) baseStart_546080 baseEnd_546080 := by
    simpa [prefixWord, tailWord_546080, baseEnd_546080] using wordTrace_append hprefix tailTrace_546080
  have hstable : (prefixWord ++ tailWord_546080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546080).length < 2 ^ (prefixWord ++ tailWord_546080).sum := by decide
  have hdescent : baseEnd_546080 < baseStart_546080 := by decide
  rcases family_descends (prefixWord ++ tailWord_546080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546090 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_546090 : Nat := 118140960795 + 546090 * 2 ^ 59
def prefixEnd_546090 : Nat := 4983230072969 + 3 ^ 40 * 546090 * 2
def baseEnd_546090 : Nat := 249250356101221025834297

theorem tailTrace_546090 : CollatzResearch.WordTrace tailWord_546090 prefixEnd_546090 249250356101221025834297 := by
  unfold tailWord_546090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979384647904167397980931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13278359061077779727949149 4979384647904167397980931)
  ·
    refine ⟨7469076971856251096971397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4979384647904167397980931 7469076971856251096971397)
    ·
      refine ⟨1400451932223047080682137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7469076971856251096971397 1400451932223047080682137)
      ·
        refine ⟨1050338949167285310511603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400451932223047080682137 1050338949167285310511603)
        ·
          refine ⟨1575508423750927965767405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050338949167285310511603 1575508423750927965767405)
          ·
            refine ⟨590815658906597987162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1575508423750927965767405 590815658906597987162777)
            ·
              refine ⟨443111744179948490372083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590815658906597987162777 443111744179948490372083)
              ·
                refine ⟨664667616269922735558125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443111744179948490372083 664667616269922735558125)
                ·
                  refine ⟨249250356101221025834297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664667616269922735558125 249250356101221025834297)
                  ·
                    rfl

theorem cell20_546090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_546090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546090 prefixEnd_546090 := by exact prefixLift 546090
  have htrace : WordTrace (prefixWord ++ tailWord_546090) baseStart_546090 baseEnd_546090 := by
    simpa [prefixWord, tailWord_546090, baseEnd_546090] using wordTrace_append hprefix tailTrace_546090
  have hstable : (prefixWord ++ tailWord_546090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546090).length < 2 ^ (prefixWord ++ tailWord_546090).sum := by decide
  have hdescent : baseEnd_546090 < baseStart_546090 := by decide
  rcases family_descends (prefixWord ++ tailWord_546090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546125 : List Nat := [1, 6, 1, 3, 1, 8]
def baseStart_546125 : Nat := 118140960795 + 546125 * 2 ^ 59
def prefixEnd_546125 : Nat := 4983230072969 + 3 ^ 40 * 546125 * 2
def baseEnd_546125 : Nat := 9232086335367276283981

theorem tailTrace_546125 : CollatzResearch.WordTrace tailWord_546125 prefixEnd_546125 9232086335367276283981 := by
  unfold tailWord_546125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918815146489870569447829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279210097659913712965219 19918815146489870569447829)
  ·
    refine ⟨933694459991712682942867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19918815146489870569447829 933694459991712682942867)
    ·
      refine ⟨1400541689987569024414301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933694459991712682942867 1400541689987569024414301)
      ·
        refine ⟨525203133745338384155363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1400541689987569024414301 525203133745338384155363)
        ·
          refine ⟨787804700618007576233045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525203133745338384155363 787804700618007576233045)
          ·
            refine ⟨9232086335367276283981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 787804700618007576233045 9232086335367276283981)
            ·
              rfl

theorem cell20_546125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_546125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546125 prefixEnd_546125 := by exact prefixLift 546125
  have htrace : WordTrace (prefixWord ++ tailWord_546125) baseStart_546125 baseEnd_546125 := by
    simpa [prefixWord, tailWord_546125, baseEnd_546125] using wordTrace_append hprefix tailTrace_546125
  have hstable : (prefixWord ++ tailWord_546125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546125).length < 2 ^ (prefixWord ++ tailWord_546125).sum := by decide
  have hdescent : baseEnd_546125 < baseStart_546125 := by decide
  rcases family_descends (prefixWord ++ tailWord_546125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546132 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_546132 : Nat := 118140960795 + 546132 * 2 ^ 59
def prefixEnd_546132 : Nat := 4983230072969 + 3 ^ 40 * 546132 * 2
def baseEnd_546132 : Nat := 249269526045655546434125

theorem tailTrace_546132 : CollatzResearch.WordTrace tailWord_546132 prefixEnd_546132 249269526045655546434125 := by
  unfold tailWord_546132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959535228732255382476325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13279380304976340509968433 9959535228732255382476325)
  ·
    refine ⟨1867412855387297884214311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9959535228732255382476325 1867412855387297884214311)
    ·
      refine ⟨2801119283080946826321467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867412855387297884214311 2801119283080946826321467)
      ·
        refine ⟨4201678924621420239482201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801119283080946826321467 4201678924621420239482201)
        ·
          refine ⟨3151259193466065179611651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4201678924621420239482201 3151259193466065179611651)
          ·
            refine ⟨4726888790199097769417477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151259193466065179611651 4726888790199097769417477)
            ·
              refine ⟨886291648162330831765777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4726888790199097769417477 886291648162330831765777)
              ·
                refine ⟨664718736121748123824333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886291648162330831765777 664718736121748123824333)
                ·
                  refine ⟨249269526045655546434125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664718736121748123824333 249269526045655546434125)
                  ·
                    rfl

theorem cell20_546132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_546132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546132 prefixEnd_546132 := by exact prefixLift 546132
  have htrace : WordTrace (prefixWord ++ tailWord_546132) baseStart_546132 baseEnd_546132 := by
    simpa [prefixWord, tailWord_546132, baseEnd_546132] using wordTrace_append hprefix tailTrace_546132
  have hstable : (prefixWord ++ tailWord_546132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546132).length < 2 ^ (prefixWord ++ tailWord_546132).sum := by decide
  have hdescent : baseEnd_546132 < baseStart_546132 := by decide
  rcases family_descends (prefixWord ++ tailWord_546132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546135 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 2]
def baseStart_546135 : Nat := 118140960795 + 546135 * 2 ^ 59
def prefixEnd_546135 : Nat := 4983230072969 + 3 ^ 40 * 546135 * 2
def baseEnd_546135 : Nat := 249270895327400869334113

theorem tailTrace_546135 : CollatzResearch.WordTrace tailWord_546135 prefixEnd_546135 249270895327400869334113 := by
  unfold tailWord_546135
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919179876453642277311859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279453250969094851541239 19919179876453642277311859)
  ·
    refine ⟨29878769814680463415967789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19919179876453642277311859 29878769814680463415967789)
    ·
      refine ⟨11204538680505173780987921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29878769814680463415967789 11204538680505173780987921)
      ·
        refine ⟨8403404010378880335740941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11204538680505173780987921 8403404010378880335740941)
        ·
          refine ⟨3151276503892080125902853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8403404010378880335740941 3151276503892080125902853)
          ·
            refine ⟨590864344479765023606785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3151276503892080125902853 590864344479765023606785)
            ·
              refine ⟨443148258359823767705089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590864344479765023606785 443148258359823767705089)
              ·
                refine ⟨332361193769867825778817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443148258359823767705089 332361193769867825778817)
                ·
                  refine ⟨249270895327400869334113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332361193769867825778817 249270895327400869334113)
                  ·
                    rfl

theorem cell20_546135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2].length) (baseStart_546135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546135 prefixEnd_546135 := by exact prefixLift 546135
  have htrace : WordTrace (prefixWord ++ tailWord_546135) baseStart_546135 baseEnd_546135 := by
    simpa [prefixWord, tailWord_546135, baseEnd_546135] using wordTrace_append hprefix tailTrace_546135
  have hstable : (prefixWord ++ tailWord_546135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546135).length < 2 ^ (prefixWord ++ tailWord_546135).sum := by decide
  have hdescent : baseEnd_546135 < baseStart_546135 := by decide
  rcases family_descends (prefixWord ++ tailWord_546135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546160 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_546160 : Nat := 118140960795 + 546160 * 2 ^ 59
def prefixEnd_546160 : Nat := 4983230072969 + 3 ^ 40 * 546160 * 2
def baseEnd_546160 : Nat := 249282306008611893500677

theorem tailTrace_546160 : CollatzResearch.WordTrace tailWord_546160 prefixEnd_546160 249282306008611893500677 := by
  unfold tailWord_546160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960045850681535773485967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13280061134242047697981289 9960045850681535773485967)
  ·
    refine ⟨14940068776022303660228951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9960045850681535773485967 14940068776022303660228951)
    ·
      refine ⟨22410103164033455490343427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14940068776022303660228951 22410103164033455490343427)
      ·
        refine ⟨33615154746050183235515141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22410103164033455490343427 33615154746050183235515141)
        ·
          refine ⟨6302841514884409356659089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33615154746050183235515141 6302841514884409356659089)
          ·
            refine ⟨4727131136163307017494317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6302841514884409356659089 4727131136163307017494317)
            ·
              refine ⟨1772674176061240131560369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4727131136163307017494317 1772674176061240131560369)
              ·
                refine ⟨1329505632045930098670277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772674176061240131560369 1329505632045930098670277)
                ·
                  refine ⟨249282306008611893500677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329505632045930098670277 249282306008611893500677)
                  ·
                    rfl

theorem cell20_546160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_546160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546160 prefixEnd_546160 := by exact prefixLift 546160
  have htrace : WordTrace (prefixWord ++ tailWord_546160) baseStart_546160 baseEnd_546160 := by
    simpa [prefixWord, tailWord_546160, baseEnd_546160] using wordTrace_append hprefix tailTrace_546160
  have hstable : (prefixWord ++ tailWord_546160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546160).length < 2 ^ (prefixWord ++ tailWord_546160).sum := by decide
  have hdescent : baseEnd_546160 < baseStart_546160 := by decide
  rcases family_descends (prefixWord ++ tailWord_546160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546204 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_546204 : Nat := 118140960795 + 546204 * 2 ^ 59
def prefixEnd_546204 : Nat := 4983230072969 + 3 ^ 40 * 546204 * 2
def baseEnd_546204 : Nat := 249302388807543296033831

theorem tailTrace_546204 : CollatzResearch.WordTrace tailWord_546204 prefixEnd_546204 249302388807543296033831 := by
  unfold tailWord_546204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960848256601833530786833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13281131008802444707715777 9960848256601833530786833)
  ·
    refine ⟨7470636192451375148090125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9960848256601833530786833 7470636192451375148090125)
    ·
      refine ⟨2801488572169265680533797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7470636192451375148090125 2801488572169265680533797)
      ·
        refine ⟨525279107281737315100087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2801488572169265680533797 525279107281737315100087)
        ·
          refine ⟨787918660922605972650131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525279107281737315100087 787918660922605972650131)
          ·
            refine ⟨1181877991383908958975197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787918660922605972650131 1181877991383908958975197)
            ·
              refine ⟨443204246768965859615699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1181877991383908958975197 443204246768965859615699)
              ·
                refine ⟨664806370153448789423549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443204246768965859615699 664806370153448789423549)
                ·
                  refine ⟨249302388807543296033831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664806370153448789423549 249302388807543296033831)
                  ·
                    rfl

theorem cell20_546204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_546204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546204 prefixEnd_546204 := by exact prefixLift 546204
  have htrace : WordTrace (prefixWord ++ tailWord_546204) baseStart_546204 baseEnd_546204 := by
    simpa [prefixWord, tailWord_546204, baseEnd_546204] using wordTrace_append hprefix tailTrace_546204
  have hstable : (prefixWord ++ tailWord_546204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546204).length < 2 ^ (prefixWord ++ tailWord_546204).sum := by decide
  have hdescent : baseEnd_546204 < baseStart_546204 := by decide
  rcases family_descends (prefixWord ++ tailWord_546204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546208 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_546208 : Nat := 118140960795 + 546208 * 2 ^ 59
def prefixEnd_546208 : Nat := 4983230072969 + 3 ^ 40 * 546208 * 2
def baseEnd_546208 : Nat := 249304214516537059900481

theorem tailTrace_546208 : CollatzResearch.WordTrace tailWord_546208 prefixEnd_546208 249304214516537059900481 := by
  unfold tailWord_546208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960921202594587872359639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13281228270126117163146185 9960921202594587872359639)
  ·
    refine ⟨14941381803891881808539459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9960921202594587872359639 14941381803891881808539459)
    ·
      refine ⟨22412072705837822712809189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14941381803891881808539459 22412072705837822712809189)
      ·
        refine ⟨4202263632344591758651723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22412072705837822712809189 4202263632344591758651723)
        ·
          refine ⟨6303395448516887637977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202263632344591758651723 6303395448516887637977585)
          ·
            refine ⟨4727546586387665728483189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6303395448516887637977585 4727546586387665728483189)
            ·
              refine ⟨443207492473843662045299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4727546586387665728483189 443207492473843662045299)
              ·
                refine ⟨664811238710765493067949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443207492473843662045299 664811238710765493067949)
                ·
                  refine ⟨249304214516537059900481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664811238710765493067949 249304214516537059900481)
                  ·
                    rfl

theorem cell20_546208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_546208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546208 prefixEnd_546208 := by exact prefixLift 546208
  have htrace : WordTrace (prefixWord ++ tailWord_546208) baseStart_546208 baseEnd_546208 := by
    simpa [prefixWord, tailWord_546208, baseEnd_546208] using wordTrace_append hprefix tailTrace_546208
  have hstable : (prefixWord ++ tailWord_546208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546208).length < 2 ^ (prefixWord ++ tailWord_546208).sum := by decide
  have hdescent : baseEnd_546208 < baseStart_546208 := by decide
  rcases family_descends (prefixWord ++ tailWord_546208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_546219 : Nat := 118140960795 + 546219 * 2 ^ 59
def prefixEnd_546219 : Nat := 4983230072969 + 3 ^ 40 * 546219 * 2
def baseEnd_546219 : Nat := 249309235216269910533769

theorem tailTrace_546219 : CollatzResearch.WordTrace tailWord_546219 prefixEnd_546219 249309235216269910533769 := by
  unfold tailWord_546219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19922243608149324623369711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13281495738766216415579807 19922243608149324623369711)
  ·
    refine ⟨29883365412223986935054567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19922243608149324623369711 29883365412223986935054567)
    ·
      refine ⟨44825048118335980402581851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29883365412223986935054567 44825048118335980402581851)
      ·
        refine ⟨67237572177503970603872777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44825048118335980402581851 67237572177503970603872777)
        ·
          refine ⟨50428179133127977952904583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67237572177503970603872777 50428179133127977952904583)
          ·
            refine ⟨75642268699691966929356875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50428179133127977952904583 75642268699691966929356875)
            ·
              refine ⟨113463403049537950394035313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75642268699691966929356875 113463403049537950394035313)
              ·
                refine ⟨85097552287153462795526485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113463403049537950394035313 85097552287153462795526485)
                ·
                  refine ⟨249309235216269910533769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85097552287153462795526485 249309235216269910533769)
                  ·
                    rfl

theorem cell20_546219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_546219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546219 prefixEnd_546219 := by exact prefixLift 546219
  have htrace : WordTrace (prefixWord ++ tailWord_546219) baseStart_546219 baseEnd_546219 := by
    simpa [prefixWord, tailWord_546219, baseEnd_546219] using wordTrace_append hprefix tailTrace_546219
  have hstable : (prefixWord ++ tailWord_546219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546219).length < 2 ^ (prefixWord ++ tailWord_546219).sum := by decide
  have hdescent : baseEnd_546219 < baseStart_546219 := by decide
  rcases family_descends (prefixWord ++ tailWord_546219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546229 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_546229 : Nat := 118140960795 + 546229 * 2 ^ 59
def prefixEnd_546229 : Nat := 4983230072969 + 3 ^ 40 * 546229 * 2
def baseEnd_546229 : Nat := 249313799488754320200395

theorem tailTrace_546229 : CollatzResearch.WordTrace tailWord_546229 prefixEnd_546229 249313799488754320200395 := by
  unfold tailWord_546229
  simp only [CollatzResearch.WordTrace]
  refine ⟨19922608338113096331233741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13281738892075397554155827 19922608338113096331233741)
  ·
    refine ⟨7470978126792411124212653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19922608338113096331233741 7470978126792411124212653)
    ·
      refine ⟨2801616797547154171579745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7470978126792411124212653 2801616797547154171579745)
      ·
        refine ⟨2101212598160365628684809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2801616797547154171579745 2101212598160365628684809)
        ·
          refine ⟨1575909448620274221513607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101212598160365628684809 1575909448620274221513607)
          ·
            refine ⟨2363864172930411332270411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575909448620274221513607 2363864172930411332270411)
            ·
              refine ⟨3545796259395616998405617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363864172930411332270411 3545796259395616998405617)
              ·
                refine ⟨2659347194546712748804213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545796259395616998405617 2659347194546712748804213)
                ·
                  refine ⟨249313799488754320200395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2659347194546712748804213 249313799488754320200395)
                  ·
                    rfl

theorem cell20_546229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_546229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546229 prefixEnd_546229 := by exact prefixLift 546229
  have htrace : WordTrace (prefixWord ++ tailWord_546229) baseStart_546229 baseEnd_546229 := by
    simpa [prefixWord, tailWord_546229, baseEnd_546229] using wordTrace_append hprefix tailTrace_546229
  have hstable : (prefixWord ++ tailWord_546229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546229).length < 2 ^ (prefixWord ++ tailWord_546229).sum := by decide
  have hdescent : baseEnd_546229 < baseStart_546229 := by decide
  rcases family_descends (prefixWord ++ tailWord_546229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546295 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_546295 : Nat := 118140960795 + 546295 * 2 ^ 59
def prefixEnd_546295 : Nat := 4983230072969 + 3 ^ 40 * 546295 * 2
def baseEnd_546295 : Nat := 249343923687151424000125

theorem tailTrace_546295 : CollatzResearch.WordTrace tailWord_546295 prefixEnd_546295 249343923687151424000125 := by
  unfold tailWord_546295
  simp only [CollatzResearch.WordTrace]
  refine ⟨19925015555873989603136339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13283343703915993068757559 19925015555873989603136339)
  ·
    refine ⟨29887523333810984404704509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19925015555873989603136339 29887523333810984404704509)
    ·
      refine ⟨11207821250179119151764191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29887523333810984404704509 11207821250179119151764191)
      ·
        refine ⟨16811731875268678727646287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207821250179119151764191 16811731875268678727646287)
        ·
          refine ⟨25217597812903018091469431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16811731875268678727646287 25217597812903018091469431)
          ·
            refine ⟨37826396719354527137204147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25217597812903018091469431 37826396719354527137204147)
            ·
              refine ⟨56739595079031790705806221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37826396719354527137204147 56739595079031790705806221)
              ·
                refine ⟨21277348154636921514677333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56739595079031790705806221 21277348154636921514677333)
                ·
                  refine ⟨249343923687151424000125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21277348154636921514677333 249343923687151424000125)
                  ·
                    rfl

theorem cell20_546295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_546295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546295 prefixEnd_546295 := by exact prefixLift 546295
  have htrace : WordTrace (prefixWord ++ tailWord_546295) baseStart_546295 baseEnd_546295 := by
    simpa [prefixWord, tailWord_546295, baseEnd_546295] using wordTrace_append hprefix tailTrace_546295
  have hstable : (prefixWord ++ tailWord_546295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546295).length < 2 ^ (prefixWord ++ tailWord_546295).sum := by decide
  have hdescent : baseEnd_546295 < baseStart_546295 := by decide
  rcases family_descends (prefixWord ++ tailWord_546295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546315 : List Nat := [1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_546315 : Nat := 118140960795 + 546315 * 2 ^ 59
def prefixEnd_546315 : Nat := 4983230072969 + 3 ^ 40 * 546315 * 2
def baseEnd_546315 : Nat := 83117684077373414444459

theorem tailTrace_546315 : CollatzResearch.WordTrace tailWord_546315 prefixEnd_546315 83117684077373414444459 := by
  unfold tailWord_546315
  simp only [CollatzResearch.WordTrace]
  refine ⟨19925745015801533018864399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13283830010534355345909599 19925745015801533018864399)
  ·
    refine ⟨29888617523702299528296599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19925745015801533018864399 29888617523702299528296599)
    ·
      refine ⟨44832926285553449292444899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29888617523702299528296599 44832926285553449292444899)
      ·
        refine ⟨67249389428330173938667349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44832926285553449292444899 67249389428330173938667349)
        ·
          refine ⟨394039391181622112921879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 67249389428330173938667349 394039391181622112921879)
          ·
            refine ⟨591059086772433169382819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394039391181622112921879 591059086772433169382819)
            ·
              refine ⟨886588630158649754074229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591059086772433169382819 886588630158649754074229)
              ·
                refine ⟨83117684077373414444459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 886588630158649754074229 83117684077373414444459)
                ·
                  rfl

theorem cell20_546315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_546315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546315 prefixEnd_546315 := by exact prefixLift 546315
  have htrace : WordTrace (prefixWord ++ tailWord_546315) baseStart_546315 baseEnd_546315 := by
    simpa [prefixWord, tailWord_546315, baseEnd_546315] using wordTrace_append hprefix tailTrace_546315
  have hstable : (prefixWord ++ tailWord_546315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546315).length < 2 ^ (prefixWord ++ tailWord_546315).sum := by decide
  have hdescent : baseEnd_546315 < baseStart_546315 := by decide
  rcases family_descends (prefixWord ++ tailWord_546315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546346 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_546346 : Nat := 118140960795 + 546346 * 2 ^ 59
def prefixEnd_546346 : Nat := 4983230072969 + 3 ^ 40 * 546346 * 2
def baseEnd_546346 : Nat := 249367201476821913299917

theorem tailTrace_546346 : CollatzResearch.WordTrace tailWord_546346 prefixEnd_546346 249367201476821913299917 := by
  unfold tailWord_546346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981718919672306328310723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13284583785792816875495261 4981718919672306328310723)
  ·
    refine ⟨7472578379508459492466085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981718919672306328310723 7472578379508459492466085)
    ·
      refine ⟨1401108446157836154837391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7472578379508459492466085 1401108446157836154837391)
      ·
        refine ⟨2101662669236754232256087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401108446157836154837391 2101662669236754232256087)
        ·
          refine ⟨3152494003855131348384131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101662669236754232256087 3152494003855131348384131)
          ·
            refine ⟨4728741005782697022576197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152494003855131348384131 4728741005782697022576197)
            ·
              refine ⟨886638938584255691733037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4728741005782697022576197 886638938584255691733037)
              ·
                refine ⟨332489601969095884399889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 886638938584255691733037 332489601969095884399889)
                ·
                  refine ⟨249367201476821913299917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332489601969095884399889 249367201476821913299917)
                  ·
                    rfl

theorem cell20_546346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_546346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546346 prefixEnd_546346 := by exact prefixLift 546346
  have htrace : WordTrace (prefixWord ++ tailWord_546346) baseStart_546346 baseEnd_546346 := by
    simpa [prefixWord, tailWord_546346, baseEnd_546346] using wordTrace_append hprefix tailTrace_546346
  have hstable : (prefixWord ++ tailWord_546346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546346).length < 2 ^ (prefixWord ++ tailWord_546346).sum := by decide
  have hdescent : baseEnd_546346 < baseStart_546346 := by decide
  rcases family_descends (prefixWord ++ tailWord_546346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546357 : List Nat := [1, 3, 3, 1, 1, 4, 7]
def baseStart_546357 : Nat := 118140960795 + 546357 * 2 ^ 59
def prefixEnd_546357 : Nat := 4983230072969 + 3 ^ 40 * 546357 * 2
def baseEnd_546357 : Nat := 27708024686283862659245

theorem tailTrace_546357 : CollatzResearch.WordTrace tailWord_546357 prefixEnd_546357 27708024686283862659245 := by
  unfold tailWord_546357
  simp only [CollatzResearch.WordTrace]
  refine ⟨19927276881649374191893325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13284851254432916127928883 19927276881649374191893325)
  ·
    refine ⟨7472728830618515321959997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19927276881649374191893325 7472728830618515321959997)
    ·
      refine ⟨2802273311481943245734999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7472728830618515321959997 2802273311481943245734999)
      ·
        refine ⟨4203409967222914868602499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802273311481943245734999 4203409967222914868602499)
        ·
          refine ⟨6305114950834372302903749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203409967222914868602499 6305114950834372302903749)
          ·
            refine ⟨1182209053281444806794453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6305114950834372302903749 1182209053281444806794453)
            ·
              refine ⟨27708024686283862659245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1182209053281444806794453 27708024686283862659245)
              ·
                rfl

theorem cell20_546357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_546357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546357 prefixEnd_546357 := by exact prefixLift 546357
  have htrace : WordTrace (prefixWord ++ tailWord_546357) baseStart_546357 baseEnd_546357 := by
    simpa [prefixWord, tailWord_546357, baseEnd_546357] using wordTrace_append hprefix tailTrace_546357
  have hstable : (prefixWord ++ tailWord_546357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546357).length < 2 ^ (prefixWord ++ tailWord_546357).sum := by decide
  have hdescent : baseEnd_546357 < baseStart_546357 := by decide
  rcases family_descends (prefixWord ++ tailWord_546357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546360 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_546360 : Nat := 118140960795 + 546360 * 2 ^ 59
def prefixEnd_546360 : Nat := 4983230072969 + 3 ^ 40 * 546360 * 2
def baseEnd_546360 : Nat := 249373591458300086833193

theorem tailTrace_546360 : CollatzResearch.WordTrace tailWord_546360 prefixEnd_546360 249373591458300086833193 := by
  unfold tailWord_546360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963693150319252852126267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13284924200425670469501689 9963693150319252852126267)
  ·
    refine ⟨14945539725478879278189401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9963693150319252852126267 14945539725478879278189401)
    ·
      refine ⟨11209154794109159458642051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14945539725478879278189401 11209154794109159458642051)
      ·
        refine ⟨16813732191163739187963077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11209154794109159458642051 16813732191163739187963077)
        ·
          refine ⟨3152574785843201097743077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16813732191163739187963077 3152574785843201097743077)
          ·
            refine ⟨591107772345600205826827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3152574785843201097743077 591107772345600205826827)
            ·
              refine ⟨886661658518400308740241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591107772345600205826827 886661658518400308740241)
              ·
                refine ⟨664996243888800231555181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886661658518400308740241 664996243888800231555181)
                ·
                  refine ⟨249373591458300086833193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664996243888800231555181 249373591458300086833193)
                  ·
                    rfl

theorem cell20_546360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_546360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546360 prefixEnd_546360 := by exact prefixLift 546360
  have htrace : WordTrace (prefixWord ++ tailWord_546360) baseStart_546360 baseEnd_546360 := by
    simpa [prefixWord, tailWord_546360, baseEnd_546360] using wordTrace_append hprefix tailTrace_546360
  have hstable : (prefixWord ++ tailWord_546360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546360).length < 2 ^ (prefixWord ++ tailWord_546360).sum := by decide
  have hdescent : baseEnd_546360 < baseStart_546360 := by decide
  rcases family_descends (prefixWord ++ tailWord_546360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546367 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 2]
def baseStart_546367 : Nat := 118140960795 + 546367 * 2 ^ 59
def prefixEnd_546367 : Nat := 4983230072969 + 3 ^ 40 * 546367 * 2
def baseEnd_546367 : Nat := 249376786449039173599831

theorem tailTrace_546367 : CollatzResearch.WordTrace tailWord_546367 prefixEnd_546367 249376786449039173599831 := by
  unfold tailWord_546367
  simp only [CollatzResearch.WordTrace]
  refine ⟨19927641611613145899757355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13285094407742097266504903 19927641611613145899757355)
  ·
    refine ⟨29891462417419718849636033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19927641611613145899757355 29891462417419718849636033)
    ·
      refine ⟨22418596813064789137227025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29891462417419718849636033 22418596813064789137227025)
      ·
        refine ⟨16813947609798591852920269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22418596813064789137227025 16813947609798591852920269)
        ·
          refine ⟨6305230353674471944845101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16813947609798591852920269 6305230353674471944845101)
          ·
            refine ⟨2364461382627926979316913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6305230353674471944845101 2364461382627926979316913)
            ·
              refine ⟨1773346036970945234487685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364461382627926979316913 1773346036970945234487685)
              ·
                refine ⟨332502381932052231466441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1773346036970945234487685 332502381932052231466441)
                ·
                  refine ⟨249376786449039173599831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332502381932052231466441 249376786449039173599831)
                  ·
                    rfl

theorem cell20_546367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2].length) (baseStart_546367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546367 prefixEnd_546367 := by exact prefixLift 546367
  have htrace : WordTrace (prefixWord ++ tailWord_546367) baseStart_546367 baseEnd_546367 := by
    simpa [prefixWord, tailWord_546367, baseEnd_546367] using wordTrace_append hprefix tailTrace_546367
  have hstable : (prefixWord ++ tailWord_546367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546367).length < 2 ^ (prefixWord ++ tailWord_546367).sum := by decide
  have hdescent : baseEnd_546367 < baseStart_546367 := by decide
  rcases family_descends (prefixWord ++ tailWord_546367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546388 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_546388 : Nat := 118140960795 + 546388 * 2 ^ 59
def prefixEnd_546388 : Nat := 4983230072969 + 3 ^ 40 * 546388 * 2
def baseEnd_546388 : Nat := 249386371421256433899745

theorem tailTrace_546388 : CollatzResearch.WordTrace tailWord_546388 prefixEnd_546388 249386371421256433899745 := by
  unfold tailWord_546388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9964203772268533243135909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13285605029691377657514545 9964203772268533243135909)
  ·
    refine ⟨1868288207300349983087983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9964203772268533243135909 1868288207300349983087983)
    ·
      refine ⟨2802432310950524974631975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868288207300349983087983 2802432310950524974631975)
      ·
        refine ⟨4203648466425787461947963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802432310950524974631975 4203648466425787461947963)
        ·
          refine ⟨6305472699638681192921945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203648466425787461947963 6305472699638681192921945)
          ·
            refine ⟨4729104524729010894691459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6305472699638681192921945 4729104524729010894691459)
            ·
              refine ⟨7093656787093516342037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729104524729010894691459 7093656787093516342037189)
              ·
                refine ⟨1330060647580034314131973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7093656787093516342037189 1330060647580034314131973)
                ·
                  refine ⟨249386371421256433899745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330060647580034314131973 249386371421256433899745)
                  ·
                    rfl

theorem cell20_546388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_546388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546388 prefixEnd_546388 := by exact prefixLift 546388
  have htrace : WordTrace (prefixWord ++ tailWord_546388) baseStart_546388 baseEnd_546388 := by
    simpa [prefixWord, tailWord_546388, baseEnd_546388] using wordTrace_append hprefix tailTrace_546388
  have hstable : (prefixWord ++ tailWord_546388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546388).length < 2 ^ (prefixWord ++ tailWord_546388).sum := by decide
  have hdescent : baseEnd_546388 < baseStart_546388 := by decide
  rcases family_descends (prefixWord ++ tailWord_546388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546397 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 2]
def baseStart_546397 : Nat := 118140960795 + 546397 * 2 ^ 59
def prefixEnd_546397 : Nat := 4983230072969 + 3 ^ 40 * 546397 * 2
def baseEnd_546397 : Nat := 249390479266492402599709

theorem tailTrace_546397 : CollatzResearch.WordTrace tailWord_546397 prefixEnd_546397 249390479266492402599709 := by
  unfold tailWord_546397
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928735801504461023349445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13285823867669640682232963 19928735801504461023349445)
  ·
    refine ⟨3736637962782086441878021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19928735801504461023349445 3736637962782086441878021)
    ·
      refine ⟨700619618021641207852129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3736637962782086441878021 700619618021641207852129)
      ·
        refine ⟨525464713516230905889097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700619618021641207852129 525464713516230905889097)
        ·
          refine ⟨394098535137173179416823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525464713516230905889097 394098535137173179416823)
          ·
            refine ⟨591147802705759769125235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394098535137173179416823 591147802705759769125235)
            ·
              refine ⟨886721704058639653687853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591147802705759769125235 886721704058639653687853)
              ·
                refine ⟨332520639021989870132945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 886721704058639653687853 332520639021989870132945)
                ·
                  refine ⟨249390479266492402599709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332520639021989870132945 249390479266492402599709)
                  ·
                    rfl

theorem cell20_546397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_546397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546397 prefixEnd_546397 := by exact prefixLift 546397
  have htrace : WordTrace (prefixWord ++ tailWord_546397) baseStart_546397 baseEnd_546397 := by
    simpa [prefixWord, tailWord_546397, baseEnd_546397] using wordTrace_append hprefix tailTrace_546397
  have hstable : (prefixWord ++ tailWord_546397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546397).length < 2 ^ (prefixWord ++ tailWord_546397).sum := by decide
  have hdescent : baseEnd_546397 < baseStart_546397 := by decide
  rcases family_descends (prefixWord ++ tailWord_546397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546409 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_546409 : Nat := 118140960795 + 546409 * 2 ^ 59
def prefixEnd_546409 : Nat := 4983230072969 + 3 ^ 40 * 546409 * 2
def baseEnd_546409 : Nat := 249395956393473694199659

theorem tailTrace_546409 : CollatzResearch.WordTrace tailWord_546409 prefixEnd_546409 249395956393473694199659 := by
  unfold tailWord_546409
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929173477460987072786281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13286115651640658048524187 19929173477460987072786281)
  ·
    refine ⟨14946880108095740304589711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19929173477460987072786281 14946880108095740304589711)
    ·
      refine ⟨22420320162143610456884567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14946880108095740304589711 22420320162143610456884567)
      ·
        refine ⟨33630480243215415685326851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22420320162143610456884567 33630480243215415685326851)
        ·
          refine ⟨50445720364823123527990277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33630480243215415685326851 50445720364823123527990277)
          ·
            refine ⟨9458572568404335661498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50445720364823123527990277 9458572568404335661498177)
            ·
              refine ⟨7093929426303251746123633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9458572568404335661498177 7093929426303251746123633)
              ·
                refine ⟨5320447069727438809592725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7093929426303251746123633 5320447069727438809592725)
                ·
                  refine ⟨249395956393473694199659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5320447069727438809592725 249395956393473694199659)
                  ·
                    rfl

theorem cell20_546409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_546409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546409 prefixEnd_546409 := by exact prefixLift 546409
  have htrace : WordTrace (prefixWord ++ tailWord_546409) baseStart_546409 baseEnd_546409 := by
    simpa [prefixWord, tailWord_546409, baseEnd_546409] using wordTrace_append hprefix tailTrace_546409
  have hstable : (prefixWord ++ tailWord_546409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546409).length < 2 ^ (prefixWord ++ tailWord_546409).sum := by decide
  have hdescent : baseEnd_546409 < baseStart_546409 := by decide
  rcases family_descends (prefixWord ++ tailWord_546409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546422 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_546422 : Nat := 118140960795 + 546422 * 2 ^ 59
def prefixEnd_546422 : Nat := 4983230072969 + 3 ^ 40 * 546422 * 2
def baseEnd_546422 : Nat := 249401889947703426766273

theorem tailTrace_546422 : CollatzResearch.WordTrace tailWord_546422 prefixEnd_546422 249401889947703426766273 := by
  unfold tailWord_546422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245602976650868143313095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13286431750942593528673013 1245602976650868143313095)
  ·
    refine ⟨1868404464976302214969643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245602976650868143313095 1868404464976302214969643)
    ·
      refine ⟨2802606697464453322454465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868404464976302214969643 2802606697464453322454465)
      ·
        refine ⟨2101955023098339991840849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802606697464453322454465 2101955023098339991840849)
        ·
          refine ⟨1576466267323754993880637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101955023098339991840849 1576466267323754993880637)
          ·
            refine ⟨591174850246408122705239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1576466267323754993880637 591174850246408122705239)
            ·
              refine ⟨886762275369612184057859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591174850246408122705239 886762275369612184057859)
              ·
                refine ⟨1330143413054418276086789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886762275369612184057859 1330143413054418276086789)
                ·
                  refine ⟨249401889947703426766273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330143413054418276086789 249401889947703426766273)
                  ·
                    rfl

theorem cell20_546422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_546422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546422 prefixEnd_546422 := by exact prefixLift 546422
  have htrace : WordTrace (prefixWord ++ tailWord_546422) baseStart_546422 baseEnd_546422 := by
    simpa [prefixWord, tailWord_546422, baseEnd_546422] using wordTrace_append hprefix tailTrace_546422
  have hstable : (prefixWord ++ tailWord_546422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546422).length < 2 ^ (prefixWord ++ tailWord_546422).sum := by decide
  have hdescent : baseEnd_546422 < baseStart_546422 := by decide
  rcases family_descends (prefixWord ++ tailWord_546422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546433 : List Nat := [1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_546433 : Nat := 118140960795 + 546433 * 2 ^ 59
def prefixEnd_546433 : Nat := 4983230072969 + 3 ^ 40 * 546433 * 2
def baseEnd_546433 : Nat := 83135636882478759133187

theorem tailTrace_546433 : CollatzResearch.WordTrace tailWord_546433 prefixEnd_546433 83135636882478759133187 := by
  unfold tailWord_546433
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930048829374039171659953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13286699219582692781106635 19930048829374039171659953)
  ·
    refine ⟨14947536622030529378744965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19930048829374039171659953 14947536622030529378744965)
    ·
      refine ⟨2802663116630724258514681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14947536622030529378744965 2802663116630724258514681)
      ·
        refine ⟨2101997337473043193886011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802663116630724258514681 2101997337473043193886011)
        ·
          refine ⟨3152996006209564790829017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101997337473043193886011 3152996006209564790829017)
          ·
            refine ⟨2364747004657173593121763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152996006209564790829017 2364747004657173593121763)
            ·
              refine ⟨3547120506985760389682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364747004657173593121763 3547120506985760389682645)
              ·
                refine ⟨83135636882478759133187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3547120506985760389682645 83135636882478759133187)
                ·
                  rfl

theorem cell20_546433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_546433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546433 prefixEnd_546433 := by exact prefixLift 546433
  have htrace : WordTrace (prefixWord ++ tailWord_546433) baseStart_546433 baseEnd_546433 := by
    simpa [prefixWord, tailWord_546433, baseEnd_546433] using wordTrace_append hprefix tailTrace_546433
  have hstable : (prefixWord ++ tailWord_546433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546433).length < 2 ^ (prefixWord ++ tailWord_546433).sum := by decide
  have hdescent : baseEnd_546433 < baseStart_546433 := by decide
  rcases family_descends (prefixWord ++ tailWord_546433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546436 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_546436 : Nat := 118140960795 + 546436 * 2 ^ 59
def prefixEnd_546436 : Nat := 4983230072969 + 3 ^ 40 * 546436 * 2
def baseEnd_546436 : Nat := 249408279929181600299549

theorem tailTrace_546436 : CollatzResearch.WordTrace tailWord_546436 prefixEnd_546436 249408279929181600299549 := by
  unfold tailWord_546436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965079124181585342009581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13286772165575447122679441 9965079124181585342009581)
  ·
    refine ⟨3736904671568094503253593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9965079124181585342009581 3736904671568094503253593)
    ·
      refine ⟨2802678503676070877440195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3736904671568094503253593 2802678503676070877440195)
      ·
        refine ⟨4204017755514106316160293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802678503676070877440195 4204017755514106316160293)
        ·
          refine ⟨788253329158894934280055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4204017755514106316160293 788253329158894934280055)
          ·
            refine ⟨1182379993738342401420083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788253329158894934280055 1182379993738342401420083)
            ·
              refine ⟨1773569990607513602130125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182379993738342401420083 1773569990607513602130125)
              ·
                refine ⟨665088746477817600798797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773569990607513602130125 665088746477817600798797)
                ·
                  refine ⟨249408279929181600299549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665088746477817600798797 249408279929181600299549)
                  ·
                    rfl

theorem cell20_546436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_546436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546436 prefixEnd_546436 := by exact prefixLift 546436
  have htrace : WordTrace (prefixWord ++ tailWord_546436) baseStart_546436 baseEnd_546436 := by
    simpa [prefixWord, tailWord_546436, baseEnd_546436] using wordTrace_append hprefix tailTrace_546436
  have hstable : (prefixWord ++ tailWord_546436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546436).length < 2 ^ (prefixWord ++ tailWord_546436).sum := by decide
  have hdescent : baseEnd_546436 < baseStart_546436 := by decide
  rcases family_descends (prefixWord ++ tailWord_546436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546519 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 2]
def baseStart_546519 : Nat := 118140960795 + 546519 * 2 ^ 59
def prefixEnd_546519 : Nat := 4983230072969 + 3 ^ 40 * 546519 * 2
def baseEnd_546519 : Nat := 249446163390802200532543

theorem tailTrace_546519 : CollatzResearch.WordTrace tailWord_546519 prefixEnd_546519 249446163390802200532543 := by
  unfold tailWord_546519
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933185507062475859290611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13288790338041650572860407 19933185507062475859290611)
  ·
    refine ⟨29899778260593713788935917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933185507062475859290611 29899778260593713788935917)
    ·
      refine ⟨11212416847722642670850969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29899778260593713788935917 11212416847722642670850969)
      ·
        refine ⟨8409312635791982003138227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11212416847722642670850969 8409312635791982003138227)
        ·
          refine ⟨12613968953687973004707341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8409312635791982003138227 12613968953687973004707341)
          ·
            refine ⟨4730238357632989876765253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613968953687973004707341 4730238357632989876765253)
            ·
              refine ⟨886919692056185601893485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4730238357632989876765253 886919692056185601893485)
              ·
                refine ⟨332594884521069600710057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 886919692056185601893485 332594884521069600710057)
                ·
                  refine ⟨249446163390802200532543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332594884521069600710057 249446163390802200532543)
                  ·
                    rfl

theorem cell20_546519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2].length) (baseStart_546519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546519 prefixEnd_546519 := by exact prefixLift 546519
  have htrace : WordTrace (prefixWord ++ tailWord_546519) baseStart_546519 baseEnd_546519 := by
    simpa [prefixWord, tailWord_546519, baseEnd_546519] using wordTrace_append hprefix tailTrace_546519
  have hstable : (prefixWord ++ tailWord_546519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546519).length < 2 ^ (prefixWord ++ tailWord_546519).sum := by decide
  have hdescent : baseEnd_546519 < baseStart_546519 := by decide
  rcases family_descends (prefixWord ++ tailWord_546519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546529 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 3]
def baseStart_546529 : Nat := 118140960795 + 546529 * 2 ^ 59
def prefixEnd_546529 : Nat := 4983230072969 + 3 ^ 40 * 546529 * 2
def baseEnd_546529 : Nat := 249450727663286610199169

theorem tailTrace_546529 : CollatzResearch.WordTrace tailWord_546529 prefixEnd_546529 249450727663286610199169 := by
  unfold tailWord_546529
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933550237026247567154641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13289033491350831711436427 19933550237026247567154641)
  ·
    refine ⟨14950162677769685675365981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19933550237026247567154641 14950162677769685675365981)
    ·
      refine ⟨5606311004163632128262243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14950162677769685675365981 5606311004163632128262243)
      ·
        refine ⟨8409466506245448192393365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606311004163632128262243 8409466506245448192393365)
        ·
          refine ⟨394193742480255384018439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8409466506245448192393365 394193742480255384018439)
          ·
            refine ⟨591290613720383076027659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394193742480255384018439 591290613720383076027659)
            ·
              refine ⟨886935920580574614041489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591290613720383076027659 886935920580574614041489)
              ·
                refine ⟨665201940435430960531117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886935920580574614041489 665201940435430960531117)
                ·
                  refine ⟨249450727663286610199169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665201940435430960531117 249450727663286610199169)
                  ·
                    rfl

theorem cell20_546529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_546529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546529 prefixEnd_546529 := by exact prefixLift 546529
  have htrace : WordTrace (prefixWord ++ tailWord_546529) baseStart_546529 baseEnd_546529 := by
    simpa [prefixWord, tailWord_546529, baseEnd_546529] using wordTrace_append hprefix tailTrace_546529
  have hstable : (prefixWord ++ tailWord_546529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546529).length < 2 ^ (prefixWord ++ tailWord_546529).sum := by decide
  have hdescent : baseEnd_546529 < baseStart_546529 := by decide
  rcases family_descends (prefixWord ++ tailWord_546529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546564 : List Nat := [2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_546564 : Nat := 118140960795 + 546564 * 2 ^ 59
def prefixEnd_546564 : Nat := 4983230072969 + 3 ^ 40 * 546564 * 2
def baseEnd_546564 : Nat := 83155567538994014677453

theorem tailTrace_546564 : CollatzResearch.WordTrace tailWord_546564 prefixEnd_546564 83155567538994014677453 := by
  unfold tailWord_546564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967413395949724272339373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13289884527932965696452497 9967413395949724272339373)
  ·
    refine ⟨3737780023481146602127265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9967413395949724272339373 3737780023481146602127265)
    ·
      refine ⟨2803335017610859951595449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3737780023481146602127265 2803335017610859951595449)
      ·
        refine ⟨2102501263208144963696587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2803335017610859951595449 2102501263208144963696587)
        ·
          refine ⟨3153751894812217445544881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102501263208144963696587 3153751894812217445544881)
          ·
            refine ⟨2365313921109163084158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3153751894812217445544881 2365313921109163084158661)
            ·
              refine ⟨443496360207968078279749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2365313921109163084158661 443496360207968078279749)
              ·
                refine ⟨83155567538994014677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443496360207968078279749 83155567538994014677453)
                ·
                  rfl

theorem cell20_546564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_546564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546564 prefixEnd_546564 := by exact prefixLift 546564
  have htrace : WordTrace (prefixWord ++ tailWord_546564) baseStart_546564 baseEnd_546564 := by
    simpa [prefixWord, tailWord_546564, baseEnd_546564] using wordTrace_append hprefix tailTrace_546564
  have hstable : (prefixWord ++ tailWord_546564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546564).length < 2 ^ (prefixWord ++ tailWord_546564).sum := by decide
  have hdescent : baseEnd_546564 < baseStart_546564 := by decide
  rcases family_descends (prefixWord ++ tailWord_546564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546592 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_546592 : Nat := 118140960795 + 546592 * 2 ^ 59
def prefixEnd_546592 : Nat := 4983230072969 + 3 ^ 40 * 546592 * 2
def baseEnd_546592 : Nat := 249479482579938391098911

theorem tailTrace_546592 : CollatzResearch.WordTrace tailWord_546592 prefixEnd_546592 249479482579938391098911 := by
  unfold tailWord_546592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967924017899004663349015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13290565357198672884465353 9967924017899004663349015)
  ·
    refine ⟨14951886026848506995023523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9967924017899004663349015 14951886026848506995023523)
    ·
      refine ⟨22427829040272760492535285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951886026848506995023523 22427829040272760492535285)
      ·
        refine ⟨2102608972525571296175183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22427829040272760492535285 2102608972525571296175183)
        ·
          refine ⟨3153913458788356944262775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102608972525571296175183 3153913458788356944262775)
          ·
            refine ⟨4730870188182535416394163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153913458788356944262775 4730870188182535416394163)
            ·
              refine ⟨7096305282273803124591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730870188182535416394163 7096305282273803124591245)
              ·
                refine ⟨2661114480852676171721717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7096305282273803124591245 2661114480852676171721717)
                ·
                  refine ⟨249479482579938391098911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661114480852676171721717 249479482579938391098911)
                  ·
                    rfl

theorem cell20_546592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_546592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546592 prefixEnd_546592 := by exact prefixLift 546592
  have htrace : WordTrace (prefixWord ++ tailWord_546592) baseStart_546592 baseEnd_546592 := by
    simpa [prefixWord, tailWord_546592, baseEnd_546592] using wordTrace_append hprefix tailTrace_546592
  have hstable : (prefixWord ++ tailWord_546592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546592).length < 2 ^ (prefixWord ++ tailWord_546592).sum := by decide
  have hdescent : baseEnd_546592 < baseStart_546592 := by decide
  rcases family_descends (prefixWord ++ tailWord_546592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546609 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_546609 : Nat := 118140960795 + 546609 * 2 ^ 59
def prefixEnd_546609 : Nat := 4983230072969 + 3 ^ 40 * 546609 * 2
def baseEnd_546609 : Nat := 249487241843161887532175

theorem tailTrace_546609 : CollatzResearch.WordTrace tailWord_546609 prefixEnd_546609 249487241843161887532175 := by
  unfold tailWord_546609
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936468076736421230066881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13290978717824280820044587 19936468076736421230066881)
  ·
    refine ⟨14952351057552315922550161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19936468076736421230066881 14952351057552315922550161)
    ·
      refine ⟨11214263293164236941912621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14952351057552315922550161 11214263293164236941912621)
      ·
        refine ⟨4205348734936588853217233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11214263293164236941912621 4205348734936588853217233)
        ·
          refine ⟨3154011551202441639912925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4205348734936588853217233 3154011551202441639912925)
          ·
            refine ⟨1182754331700915614967347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3154011551202441639912925 1182754331700915614967347)
            ·
              refine ⟨1774131497551373422451021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182754331700915614967347 1774131497551373422451021)
              ·
                refine ⟨665299311581765033419133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1774131497551373422451021 665299311581765033419133)
                ·
                  refine ⟨249487241843161887532175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665299311581765033419133 249487241843161887532175)
                  ·
                    rfl

theorem cell20_546609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_546609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546609 prefixEnd_546609 := by exact prefixLift 546609
  have htrace : WordTrace (prefixWord ++ tailWord_546609) baseStart_546609 baseEnd_546609 := by
    simpa [prefixWord, tailWord_546609, baseEnd_546609] using wordTrace_append hprefix tailTrace_546609
  have hstable : (prefixWord ++ tailWord_546609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546609).length < 2 ^ (prefixWord ++ tailWord_546609).sum := by decide
  have hdescent : baseEnd_546609 < baseStart_546609 := by decide
  rcases family_descends (prefixWord ++ tailWord_546609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546682 : List Nat := [3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_546682 : Nat := 118140960795 + 546682 * 2 ^ 59
def prefixEnd_546682 : Nat := 4983230072969 + 3 ^ 40 * 546682 * 2
def baseEnd_546682 : Nat := 83173520344099359366181

theorem tailTrace_546682 : CollatzResearch.WordTrace tailWord_546682 prefixEnd_546682 83173520344099359366181 := by
  unfold tailWord_546682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984782651367988674368575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13292753736981303131649533 4984782651367988674368575)
  ·
    refine ⟨7477173977051983011552863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4984782651367988674368575 7477173977051983011552863)
    ·
      refine ⟨11215760965577974517329295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7477173977051983011552863 11215760965577974517329295)
      ·
        refine ⟨16823641448366961775993943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11215760965577974517329295 16823641448366961775993943)
        ·
          refine ⟨25235462172550442663990915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16823641448366961775993943 25235462172550442663990915)
          ·
            refine ⟨37853193258825663995986373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25235462172550442663990915 37853193258825663995986373)
            ·
              refine ⟨7097473736029811999247445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37853193258825663995986373 7097473736029811999247445)
              ·
                refine ⟨83173520344099359366181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7097473736029811999247445 83173520344099359366181)
                ·
                  rfl

theorem cell20_546682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_546682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546682 prefixEnd_546682 := by exact prefixLift 546682
  have htrace : WordTrace (prefixWord ++ tailWord_546682) baseStart_546682 baseEnd_546682 := by
    simpa [prefixWord, tailWord_546682, baseEnd_546682] using wordTrace_append hprefix tailTrace_546682
  have hstable : (prefixWord ++ tailWord_546682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546682).length < 2 ^ (prefixWord ++ tailWord_546682).sum := by decide
  have hdescent : baseEnd_546682 < baseStart_546682 := by decide
  rcases family_descends (prefixWord ++ tailWord_546682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546702 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_546702 : Nat := 118140960795 + 546702 * 2 ^ 59
def prefixEnd_546702 : Nat := 4983230072969 + 3 ^ 40 * 546702 * 2
def baseEnd_546702 : Nat := 249529689577266897431795

theorem tailTrace_546702 : CollatzResearch.WordTrace tailWord_546702 prefixEnd_546702 249529689577266897431795 := by
  unfold tailWord_546702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492482508174937264150295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13293240043599665408801573 2492482508174937264150295)
  ·
    refine ⟨3738723762262405896225443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2492482508174937264150295 3738723762262405896225443)
    ·
      refine ⟨5608085643393608844338165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3738723762262405896225443 5608085643393608844338165)
      ·
        refine ⟨525758029068150829156703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5608085643393608844338165 525758029068150829156703)
        ·
          refine ⟨788637043602226243735055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525758029068150829156703 788637043602226243735055)
          ·
            refine ⟨1182955565403339365602583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788637043602226243735055 1182955565403339365602583)
            ·
              refine ⟨1774433348105009048403875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182955565403339365602583 1774433348105009048403875)
              ·
                refine ⟨2661650022157513572605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774433348105009048403875 2661650022157513572605813)
                ·
                  refine ⟨249529689577266897431795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661650022157513572605813 249529689577266897431795)
                  ·
                    rfl

theorem cell20_546702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_546702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546702 prefixEnd_546702 := by exact prefixLift 546702
  have htrace : WordTrace (prefixWord ++ tailWord_546702) baseStart_546702 baseEnd_546702 := by
    simpa [prefixWord, tailWord_546702, baseEnd_546702] using wordTrace_append hprefix tailTrace_546702
  have hstable : (prefixWord ++ tailWord_546702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546702).length < 2 ^ (prefixWord ++ tailWord_546702).sum := by decide
  have hdescent : baseEnd_546702 < baseStart_546702 := by decide
  rcases family_descends (prefixWord ++ tailWord_546702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546713 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_546713 : Nat := 118140960795 + 546713 * 2 ^ 59
def prefixEnd_546713 : Nat := 4983230072969 + 3 ^ 40 * 546713 * 2
def baseEnd_546713 : Nat := 249534710276999748065083

theorem tailTrace_546713 : CollatzResearch.WordTrace tailWord_546713 prefixEnd_546713 249534710276999748065083 := by
  unfold tailWord_546713
  simp only [CollatzResearch.WordTrace]
  refine ⟨19940261268359646991852793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13293507512239764661235195 19940261268359646991852793)
  ·
    refine ⟨14955195951269735243889595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19940261268359646991852793 14955195951269735243889595)
    ·
      refine ⟨22432793926904602865834393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14955195951269735243889595 22432793926904602865834393)
      ·
        refine ⟨16824595445178452149375795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22432793926904602865834393 16824595445178452149375795)
        ·
          refine ⟨25236893167767678224063693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824595445178452149375795 25236893167767678224063693)
          ·
            refine ⟨9463834937912879334023885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25236893167767678224063693 9463834937912879334023885)
            ·
              refine ⟨3548938101717329750258957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9463834937912879334023885 3548938101717329750258957)
              ·
                refine ⟨1330851788143998656347109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3548938101717329750258957 1330851788143998656347109)
                ·
                  refine ⟨249534710276999748065083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330851788143998656347109 249534710276999748065083)
                  ·
                    rfl

theorem cell20_546713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_546713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546713 prefixEnd_546713 := by exact prefixLift 546713
  have htrace : WordTrace (prefixWord ++ tailWord_546713) baseStart_546713 baseEnd_546713 := by
    simpa [prefixWord, tailWord_546713, baseEnd_546713] using wordTrace_append hprefix tailTrace_546713
  have hstable : (prefixWord ++ tailWord_546713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546713).length < 2 ^ (prefixWord ++ tailWord_546713).sum := by decide
  have hdescent : baseEnd_546713 < baseStart_546713 := by decide
  rcases family_descends (prefixWord ++ tailWord_546713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546720 : List Nat := [2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_546720 : Nat := 118140960795 + 546720 * 2 ^ 59
def prefixEnd_546720 : Nat := 4983230072969 + 3 ^ 40 * 546720 * 2
def baseEnd_546720 : Nat := 83179301755912944943907

theorem tailTrace_546720 : CollatzResearch.WordTrace tailWord_546720 prefixEnd_546720 83179301755912944943907 := by
  unfold tailWord_546720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970258289667143593678807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13293677719556191458238409 9970258289667143593678807)
  ·
    refine ⟨14955387434500715390518211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9970258289667143593678807 14955387434500715390518211)
    ·
      refine ⟨22433081151751073085777317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14955387434500715390518211 22433081151751073085777317)
      ·
        refine ⟨4206202715953326203583247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22433081151751073085777317 4206202715953326203583247)
        ·
          refine ⟨6309304073929989305374871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206202715953326203583247 6309304073929989305374871)
          ·
            refine ⟨9463956110894983958062307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309304073929989305374871 9463956110894983958062307)
            ·
              refine ⟨14195934166342475937093461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9463956110894983958062307 14195934166342475937093461)
              ·
                refine ⟨83179301755912944943907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14195934166342475937093461 83179301755912944943907)
                ·
                  rfl

theorem cell20_546720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_546720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546720 prefixEnd_546720 := by exact prefixLift 546720
  have htrace : WordTrace (prefixWord ++ tailWord_546720) baseStart_546720 baseEnd_546720 := by
    simpa [prefixWord, tailWord_546720, baseEnd_546720] using wordTrace_append hprefix tailTrace_546720
  have hstable : (prefixWord ++ tailWord_546720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546720).length < 2 ^ (prefixWord ++ tailWord_546720).sum := by decide
  have hdescent : baseEnd_546720 < baseStart_546720 := by decide
  rcases family_descends (prefixWord ++ tailWord_546720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546737 : List Nat := [1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_546737 : Nat := 118140960795 + 546737 * 2 ^ 59
def prefixEnd_546737 : Nat := 4983230072969 + 3 ^ 40 * 546737 * 2
def baseEnd_546737 : Nat := 83181888176987443754995

theorem tailTrace_546737 : CollatzResearch.WordTrace tailWord_546737 prefixEnd_546737 83181888176987443754995 := by
  unfold tailWord_546737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19941136620272699090726465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13294091080181799393817643 19941136620272699090726465)
  ·
    refine ⟨14955852465204524318044849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19941136620272699090726465 14955852465204524318044849)
    ·
      refine ⟨11216889348903393238533637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14955852465204524318044849 11216889348903393238533637)
      ·
        refine ⟨2103166752919386232225057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11216889348903393238533637 2103166752919386232225057)
        ·
          refine ⟨1577375064689539674168793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103166752919386232225057 1577375064689539674168793)
          ·
            refine ⟨1183031298517154755626595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577375064689539674168793 1183031298517154755626595)
            ·
              refine ⟨1774546947775732133439893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183031298517154755626595 1774546947775732133439893)
              ·
                refine ⟨83181888176987443754995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1774546947775732133439893 83181888176987443754995)
                ·
                  rfl

theorem cell20_546737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_546737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546737 prefixEnd_546737 := by exact prefixLift 546737
  have htrace : WordTrace (prefixWord ++ tailWord_546737) baseStart_546737 baseEnd_546737 := by
    simpa [prefixWord, tailWord_546737, baseEnd_546737] using wordTrace_append hprefix tailTrace_546737
  have hstable : (prefixWord ++ tailWord_546737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546737).length < 2 ^ (prefixWord ++ tailWord_546737).sum := by decide
  have hdescent : baseEnd_546737 < baseStart_546737 := by decide
  rcases family_descends (prefixWord ++ tailWord_546737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546764 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_546764 : Nat := 118140960795 + 546764 * 2 ^ 59
def prefixEnd_546764 : Nat := 4983230072969 + 3 ^ 40 * 546764 * 2
def baseEnd_546764 : Nat := 249557988066670237364875

theorem tailTrace_546764 : CollatzResearch.WordTrace tailWord_546764 prefixEnd_546764 249557988066670237364875 := by
  unfold tailWord_546764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971060695587441350979673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13294747594116588467972897 9971060695587441350979673)
  ·
    refine ⟨7478295521690581013234755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9971060695587441350979673 7478295521690581013234755)
    ·
      refine ⟨11217443282535871519852133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478295521690581013234755 11217443282535871519852133)
      ·
        refine ⟨2103270615475475909972275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11217443282535871519852133 2103270615475475909972275)
        ·
          refine ⟨3154905923213213864958413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103270615475475909972275 3154905923213213864958413)
          ·
            refine ⟨1183089721204955199359405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3154905923213213864958413 1183089721204955199359405)
            ·
              refine ⟨443658645451858199759777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183089721204955199359405 443658645451858199759777)
              ·
                refine ⟨332743984088893649819833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443658645451858199759777 332743984088893649819833)
                ·
                  refine ⟨249557988066670237364875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332743984088893649819833 249557988066670237364875)
                  ·
                    rfl

theorem cell20_546764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_546764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546764 prefixEnd_546764 := by exact prefixLift 546764
  have htrace : WordTrace (prefixWord ++ tailWord_546764) baseStart_546764 baseEnd_546764 := by
    simpa [prefixWord, tailWord_546764, baseEnd_546764] using wordTrace_append hprefix tailTrace_546764
  have hstable : (prefixWord ++ tailWord_546764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546764).length < 2 ^ (prefixWord ++ tailWord_546764).sum := by decide
  have hdescent : baseEnd_546764 < baseStart_546764 := by decide
  rcases family_descends (prefixWord ++ tailWord_546764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546768 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_546768 : Nat := 118140960795 + 546768 * 2 ^ 59
def prefixEnd_546768 : Nat := 4983230072969 + 3 ^ 40 * 546768 * 2
def baseEnd_546768 : Nat := 249559813775664001231525

theorem tailTrace_546768 : CollatzResearch.WordTrace tailWord_546768 prefixEnd_546768 249559813775664001231525 := by
  unfold tailWord_546768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971133641580195692552479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13294844855440260923403305 9971133641580195692552479)
  ·
    refine ⟨14956700462370293538828719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9971133641580195692552479 14956700462370293538828719)
    ·
      refine ⟨22435050693555440308243079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956700462370293538828719 22435050693555440308243079)
      ·
        refine ⟨33652576040333160462364619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22435050693555440308243079 33652576040333160462364619)
        ·
          refine ⟨50478864060499740693546929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33652576040333160462364619 50478864060499740693546929)
          ·
            refine ⟨37859148045374805520160197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50478864060499740693546929 37859148045374805520160197)
            ·
              refine ⟨7098590258507776035030037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37859148045374805520160197 7098590258507776035030037)
              ·
                refine ⟨332746418367552001642033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7098590258507776035030037 332746418367552001642033)
                ·
                  refine ⟨249559813775664001231525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332746418367552001642033 249559813775664001231525)
                  ·
                    rfl

theorem cell20_546768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_546768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546768 prefixEnd_546768 := by exact prefixLift 546768
  have htrace : WordTrace (prefixWord ++ tailWord_546768) baseStart_546768 baseEnd_546768 := by
    simpa [prefixWord, tailWord_546768, baseEnd_546768] using wordTrace_append hprefix tailTrace_546768
  have hstable : (prefixWord ++ tailWord_546768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546768).length < 2 ^ (prefixWord ++ tailWord_546768).sum := by decide
  have hdescent : baseEnd_546768 < baseStart_546768 := by decide
  rcases family_descends (prefixWord ++ tailWord_546768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546774 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_546774 : Nat := 118140960795 + 546774 * 2 ^ 59
def prefixEnd_546774 : Nat := 4983230072969 + 3 ^ 40 * 546774 * 2
def baseEnd_546774 : Nat := 249562552339154647031501

theorem tailTrace_546774 : CollatzResearch.WordTrace tailWord_546774 prefixEnd_546774 249562552339154647031501 := by
  unfold tailWord_546774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246405382571165900613961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13294990747425769606548917 1246405382571165900613961)
  ·
    refine ⟨934804036928374425460471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1246405382571165900613961 934804036928374425460471)
    ·
      refine ⟨1402206055392561638190707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934804036928374425460471 1402206055392561638190707)
      ·
        refine ⟨2103309083088842457286061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402206055392561638190707 2103309083088842457286061)
        ·
          refine ⟨788740906158315921482273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2103309083088842457286061 788740906158315921482273)
          ·
            refine ⟨591555679618736941111705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788740906158315921482273 591555679618736941111705)
            ·
              refine ⟨443666759714052705833779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591555679618736941111705 443666759714052705833779)
              ·
                refine ⟨665500139571079058750669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443666759714052705833779 665500139571079058750669)
                ·
                  refine ⟨249562552339154647031501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665500139571079058750669 249562552339154647031501)
                  ·
                    rfl

theorem cell20_546774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_546774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546774 prefixEnd_546774 := by exact prefixLift 546774
  have htrace : WordTrace (prefixWord ++ tailWord_546774) baseStart_546774 baseEnd_546774 := by
    simpa [prefixWord, tailWord_546774, baseEnd_546774] using wordTrace_append hprefix tailTrace_546774
  have hstable : (prefixWord ++ tailWord_546774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546774).length < 2 ^ (prefixWord ++ tailWord_546774).sum := by decide
  have hdescent : baseEnd_546774 < baseStart_546774 := by decide
  rcases family_descends (prefixWord ++ tailWord_546774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546803 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_546803 : Nat := 118140960795 + 546803 * 2 ^ 59
def prefixEnd_546803 : Nat := 4983230072969 + 3 ^ 40 * 546803 * 2
def baseEnd_546803 : Nat := 249575788729359435064715

theorem tailTrace_546803 : CollatzResearch.WordTrace tailWord_546803 prefixEnd_546803 249575788729359435064715 := by
  unfold tailWord_546803
  simp only [CollatzResearch.WordTrace]
  refine ⟨19943543838033592362629063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13295695892022394908419375 19943543838033592362629063)
  ·
    refine ⟨29915315757050388543943595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19943543838033592362629063 29915315757050388543943595)
    ·
      refine ⟨44872973635575582815915393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29915315757050388543943595 44872973635575582815915393)
      ·
        refine ⟨33654730226681687111936545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44872973635575582815915393 33654730226681687111936545)
        ·
          refine ⟨25241047670011265333952409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33654730226681687111936545 25241047670011265333952409)
          ·
            refine ⟨18930785752508449000464307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25241047670011265333952409 18930785752508449000464307)
            ·
              refine ⟨28396178628762673500696461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18930785752508449000464307 28396178628762673500696461)
              ·
                refine ⟨10648566985786002562761173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28396178628762673500696461 10648566985786002562761173)
                ·
                  refine ⟨249575788729359435064715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10648566985786002562761173 249575788729359435064715)
                  ·
                    rfl

theorem cell20_546803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_546803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546803 prefixEnd_546803 := by exact prefixLift 546803
  have htrace : WordTrace (prefixWord ++ tailWord_546803) baseStart_546803 baseEnd_546803 := by
    simpa [prefixWord, tailWord_546803, baseEnd_546803] using wordTrace_append hprefix tailTrace_546803
  have hstable : (prefixWord ++ tailWord_546803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546803).length < 2 ^ (prefixWord ++ tailWord_546803).sum := by decide
  have hdescent : baseEnd_546803 < baseStart_546803 := by decide
  rcases family_descends (prefixWord ++ tailWord_546803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546822 : List Nat := [6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_546822 : Nat := 118140960795 + 546822 * 2 ^ 59
def prefixEnd_546822 : Nat := 4983230072969 + 3 ^ 40 * 546822 * 2
def baseEnd_546822 : Nat := 83194820282359937810435

theorem tailTrace_546822 : CollatzResearch.WordTrace tailWord_546822 prefixEnd_546822 83194820282359937810435 := by
  unfold tailWord_546822
  simp only [CollatzResearch.WordTrace]
  refine ⟨623257400780148706486585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13296157883309839071713813 623257400780148706486585)
  ·
    refine ⟨467443050585111529864939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 623257400780148706486585 467443050585111529864939)
    ·
      refine ⟨701164575877667294797409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467443050585111529864939 701164575877667294797409)
      ·
        refine ⟨525873431908250471098057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701164575877667294797409 525873431908250471098057)
        ·
          refine ⟨394405073931187853323543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525873431908250471098057 394405073931187853323543)
          ·
            refine ⟨591607610896781779985315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394405073931187853323543 591607610896781779985315)
            ·
              refine ⟨887411416345172669977973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591607610896781779985315 887411416345172669977973)
              ·
                refine ⟨83194820282359937810435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887411416345172669977973 83194820282359937810435)
                ·
                  rfl

theorem cell20_546822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_546822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546822 prefixEnd_546822 := by exact prefixLift 546822
  have htrace : WordTrace (prefixWord ++ tailWord_546822) baseStart_546822 baseEnd_546822 := by
    simpa [prefixWord, tailWord_546822, baseEnd_546822] using wordTrace_append hprefix tailTrace_546822
  have hstable : (prefixWord ++ tailWord_546822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546822).length < 2 ^ (prefixWord ++ tailWord_546822).sum := by decide
  have hdescent : baseEnd_546822 < baseStart_546822 := by decide
  rcases family_descends (prefixWord ++ tailWord_546822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546823 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 2]
def baseStart_546823 : Nat := 118140960795 + 546823 * 2 ^ 59
def prefixEnd_546823 : Nat := 4983230072969 + 3 ^ 40 * 546823 * 2
def baseEnd_546823 : Nat := 249584917274328254397967

theorem tailTrace_546823 : CollatzResearch.WordTrace tailWord_546823 prefixEnd_546823 249584917274328254397967 := by
  unfold tailWord_546823
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944273297961135778357123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296182198640757185571415 19944273297961135778357123)
  ·
    refine ⟨29916409946941703667535685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944273297961135778357123 29916409946941703667535685)
    ·
      refine ⟨5609326865051569437662941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29916409946941703667535685 5609326865051569437662941)
      ·
        refine ⟨2103497574394338539123603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5609326865051569437662941 2103497574394338539123603)
        ·
          refine ⟨3155246361591507808685405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103497574394338539123603 3155246361591507808685405)
          ·
            refine ⟨1183217385596815428257027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155246361591507808685405 1183217385596815428257027)
            ·
              refine ⟨1774826078395223142385541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183217385596815428257027 1774826078395223142385541)
              ·
                refine ⟨332779889699104339197289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1774826078395223142385541 332779889699104339197289)
                ·
                  refine ⟨249584917274328254397967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332779889699104339197289 249584917274328254397967)
                  ·
                    rfl

theorem cell20_546823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2].length) (baseStart_546823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546823 prefixEnd_546823 := by exact prefixLift 546823
  have htrace : WordTrace (prefixWord ++ tailWord_546823) baseStart_546823 baseEnd_546823 := by
    simpa [prefixWord, tailWord_546823, baseEnd_546823] using wordTrace_append hprefix tailTrace_546823
  have hstable : (prefixWord ++ tailWord_546823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546823).length < 2 ^ (prefixWord ++ tailWord_546823).sum := by decide
  have hdescent : baseEnd_546823 < baseStart_546823 := by decide
  rcases family_descends (prefixWord ++ tailWord_546823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546827 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_546827 : Nat := 118140960795 + 546827 * 2 ^ 59
def prefixEnd_546827 : Nat := 4983230072969 + 3 ^ 40 * 546827 * 2
def baseEnd_546827 : Nat := 249586742983322018264617

theorem tailTrace_546827 : CollatzResearch.WordTrace tailWord_546827 prefixEnd_546827 249586742983322018264617 := by
  unfold tailWord_546827
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944419189946644461502735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296279459964429641001823 19944419189946644461502735)
  ·
    refine ⟨29916628784919966692254103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944419189946644461502735 29916628784919966692254103)
    ·
      refine ⟨44874943177379950038381155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29916628784919966692254103 44874943177379950038381155)
      ·
        refine ⟨67312414766069925057571733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44874943177379950038381155 67312414766069925057571733)
        ·
          refine ⟨3155269442159527737073675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67312414766069925057571733 3155269442159527737073675)
          ·
            refine ⟨4732904163239291605610513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155269442159527737073675 4732904163239291605610513)
            ·
              refine ⟨3549678122429468704207885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4732904163239291605610513 3549678122429468704207885)
              ·
                refine ⟨1331129295911050764077957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3549678122429468704207885 1331129295911050764077957)
                ·
                  refine ⟨249586742983322018264617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331129295911050764077957 249586742983322018264617)
                  ·
                    rfl

theorem cell20_546827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_546827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546827 prefixEnd_546827 := by exact prefixLift 546827
  have htrace : WordTrace (prefixWord ++ tailWord_546827) baseStart_546827 baseEnd_546827 := by
    simpa [prefixWord, tailWord_546827, baseEnd_546827] using wordTrace_append hprefix tailTrace_546827
  have hstable : (prefixWord ++ tailWord_546827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546827).length < 2 ^ (prefixWord ++ tailWord_546827).sum := by decide
  have hdescent : baseEnd_546827 < baseStart_546827 := by decide
  rcases family_descends (prefixWord ++ tailWord_546827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546841 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_546841 : Nat := 118140960795 + 546841 * 2 ^ 59
def prefixEnd_546841 : Nat := 4983230072969 + 3 ^ 40 * 546841 * 2
def baseEnd_546841 : Nat := 249593132964800191797893

theorem tailTrace_546841 : CollatzResearch.WordTrace tailWord_546841 prefixEnd_546841 249593132964800191797893 := by
  unfold tailWord_546841
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944929811895924852512377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296619874597283235008251 19944929811895924852512377)
  ·
    refine ⟨14958697358921943639384283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19944929811895924852512377 14958697358921943639384283)
    ·
      refine ⟨22438046038382915459076425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14958697358921943639384283 22438046038382915459076425)
      ·
        refine ⟨16828534528787186594307319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22438046038382915459076425 16828534528787186594307319)
        ·
          refine ⟨25242801793180779891460979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16828534528787186594307319 25242801793180779891460979)
          ·
            refine ⟨37864202689771169837191469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25242801793180779891460979 37864202689771169837191469)
            ·
              refine ⟨14199076008664188688946801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37864202689771169837191469 14199076008664188688946801)
              ·
                refine ⟨10649307006498141516710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14199076008664188688946801 10649307006498141516710101)
                ·
                  refine ⟨249593132964800191797893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10649307006498141516710101 249593132964800191797893)
                  ·
                    rfl

theorem cell20_546841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_546841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546841 prefixEnd_546841 := by exact prefixLift 546841
  have htrace : WordTrace (prefixWord ++ tailWord_546841) baseStart_546841 baseEnd_546841 := by
    simpa [prefixWord, tailWord_546841, baseEnd_546841] using wordTrace_append hprefix tailTrace_546841
  have hstable : (prefixWord ++ tailWord_546841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546841).length < 2 ^ (prefixWord ++ tailWord_546841).sum := by decide
  have hdescent : baseEnd_546841 < baseStart_546841 := by decide
  rcases family_descends (prefixWord ++ tailWord_546841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546844 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_546844 : Nat := 118140960795 + 546844 * 2 ^ 59
def prefixEnd_546844 : Nat := 4983230072969 + 3 ^ 40 * 546844 * 2
def baseEnd_546844 : Nat := 249594502246545514697881

theorem tailTrace_546844 : CollatzResearch.WordTrace tailWord_546844 prefixEnd_546844 249594502246545514697881 := by
  unfold tailWord_546844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972519615442528182435793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13296692820590037576581057 9972519615442528182435793)
  ·
    refine ⟨7479389711581896136826845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9972519615442528182435793 7479389711581896136826845)
    ·
      refine ⟨2804771141843211051310067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7479389711581896136826845 2804771141843211051310067)
      ·
        refine ⟨4207156712764816576965101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804771141843211051310067 4207156712764816576965101)
        ·
          refine ⟨1577683767286806216361913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4207156712764816576965101 1577683767286806216361913)
          ·
            refine ⟨1183262825465104662271435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577683767286806216361913 1183262825465104662271435)
            ·
              refine ⟨1774894238197656993407153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183262825465104662271435 1774894238197656993407153)
              ·
                refine ⟨1331170678648242745055365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774894238197656993407153 1331170678648242745055365)
                ·
                  refine ⟨249594502246545514697881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331170678648242745055365 249594502246545514697881)
                  ·
                    rfl

theorem cell20_546844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_546844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546844 prefixEnd_546844 := by exact prefixLift 546844
  have htrace : WordTrace (prefixWord ++ tailWord_546844) baseStart_546844 baseEnd_546844 := by
    simpa [prefixWord, tailWord_546844, baseEnd_546844] using wordTrace_append hprefix tailTrace_546844
  have hstable : (prefixWord ++ tailWord_546844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546844).length < 2 ^ (prefixWord ++ tailWord_546844).sum := by decide
  have hdescent : baseEnd_546844 < baseStart_546844 := by decide
  rcases family_descends (prefixWord ++ tailWord_546844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546851 : List Nat := [1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_546851 : Nat := 118140960795 + 546851 * 2 ^ 59
def prefixEnd_546851 : Nat := 4983230072969 + 3 ^ 40 * 546851 * 2
def baseEnd_546851 : Nat := 83199232412428200488173

theorem tailTrace_546851 : CollatzResearch.WordTrace tailWord_546851 prefixEnd_546851 83199232412428200488173 := by
  unfold tailWord_546851
  simp only [CollatzResearch.WordTrace]
  refine ⟨19945294541859696560376407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296863027906464373584271 19945294541859696560376407)
  ·
    refine ⟨29917941812789544840564611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19945294541859696560376407 29917941812789544840564611)
    ·
      refine ⟨44876912719184317260846917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29917941812789544840564611 44876912719184317260846917)
      ·
        refine ⟨8414421134847059486408797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44876912719184317260846917 8414421134847059486408797)
        ·
          refine ⟨3155407925567647307403299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8414421134847059486408797 3155407925567647307403299)
          ·
            refine ⟨4733111888351470961104949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155407925567647307403299 4733111888351470961104949)
            ·
              refine ⟨443729239532950402603589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4733111888351470961104949 443729239532950402603589)
              ·
                refine ⟨83199232412428200488173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443729239532950402603589 83199232412428200488173)
                ·
                  rfl

theorem cell20_546851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_546851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546851 prefixEnd_546851 := by exact prefixLift 546851
  have htrace : WordTrace (prefixWord ++ tailWord_546851) baseStart_546851 baseEnd_546851 := by
    simpa [prefixWord, tailWord_546851, baseEnd_546851] using wordTrace_append hprefix tailTrace_546851
  have hstable : (prefixWord ++ tailWord_546851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546851).length < 2 ^ (prefixWord ++ tailWord_546851).sum := by decide
  have hdescent : baseEnd_546851 < baseStart_546851 := by decide
  rcases family_descends (prefixWord ++ tailWord_546851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546868 : List Nat := [2, 5, 1, 2, 2, 1, 7]
def baseStart_546868 : Nat := 118140960795 + 546868 * 2 ^ 59
def prefixEnd_546868 : Nat := 4983230072969 + 3 ^ 40 * 546868 * 2
def baseEnd_546868 : Nat := 27733939611167566433087

theorem tailTrace_546868 : CollatzResearch.WordTrace tailWord_546868 prefixEnd_546868 27733939611167566433087 := by
  unfold tailWord_546868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972957291399054231872629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13297276388532072309163505 9972957291399054231872629)
  ·
    refine ⟨934964746068661334238059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9972957291399054231872629 934964746068661334238059)
    ·
      refine ⟨1402447119102992001357089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934964746068661334238059 1402447119102992001357089)
      ·
        refine ⟨1051835339327244001017817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402447119102992001357089 1051835339327244001017817)
        ·
          refine ⟨788876504495433000763363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051835339327244001017817 788876504495433000763363)
          ·
            refine ⟨1183314756743149501145045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788876504495433000763363 1183314756743149501145045)
            ·
              refine ⟨27733939611167566433087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1183314756743149501145045 27733939611167566433087)
              ·
                rfl

theorem cell20_546868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_546868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546868 prefixEnd_546868 := by exact prefixLift 546868
  have htrace : WordTrace (prefixWord ++ tailWord_546868) baseStart_546868 baseEnd_546868 := by
    simpa [prefixWord, tailWord_546868, baseEnd_546868] using wordTrace_append hprefix tailTrace_546868
  have hstable : (prefixWord ++ tailWord_546868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546868).length < 2 ^ (prefixWord ++ tailWord_546868).sum := by decide
  have hdescent : baseEnd_546868 < baseStart_546868 := by decide
  rcases family_descends (prefixWord ++ tailWord_546868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546902 : List Nat := [5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_546902 : Nat := 118140960795 + 546902 * 2 ^ 59
def prefixEnd_546902 : Nat := 4983230072969 + 3 ^ 40 * 546902 * 2
def baseEnd_546902 : Nat := 83206991675651696921437

theorem tailTrace_546902 : CollatzResearch.WordTrace tailWord_546902 prefixEnd_546902 83206991675651696921437 := by
  unfold tailWord_546902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246697166542183266905185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13298103109783288180321973 1246697166542183266905185)
  ·
    refine ⟨935022874906637450178889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1246697166542183266905185 935022874906637450178889)
    ·
      refine ⟨701267156179978087634167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 935022874906637450178889 701267156179978087634167)
      ·
        refine ⟨1051900734269967131451251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701267156179978087634167 1051900734269967131451251)
        ·
          refine ⟨1577851101404950697176877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051900734269967131451251 1577851101404950697176877)
          ·
            refine ⟨591694163026856511441329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1577851101404950697176877 591694163026856511441329)
            ·
              refine ⟨443770622270142383580997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591694163026856511441329 443770622270142383580997)
              ·
                refine ⟨83206991675651696921437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443770622270142383580997 83206991675651696921437)
                ·
                  rfl

theorem cell20_546902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_546902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546902 prefixEnd_546902 := by exact prefixLift 546902
  have htrace : WordTrace (prefixWord ++ tailWord_546902) baseStart_546902 baseEnd_546902 := by
    simpa [prefixWord, tailWord_546902, baseEnd_546902] using wordTrace_append hprefix tailTrace_546902
  have hstable : (prefixWord ++ tailWord_546902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546902).length < 2 ^ (prefixWord ++ tailWord_546902).sum := by decide
  have hdescent : baseEnd_546902 < baseStart_546902 := by decide
  rcases family_descends (prefixWord ++ tailWord_546902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546903 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_546903 : Nat := 118140960795 + 546903 * 2 ^ 59
def prefixEnd_546903 : Nat := 4983230072969 + 3 ^ 40 * 546903 * 2
def baseEnd_546903 : Nat := 249621431454203531730973

theorem tailTrace_546903 : CollatzResearch.WordTrace tailWord_546903 prefixEnd_546903 249621431454203531730973 := by
  unfold tailWord_546903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19947191137671309441269363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13298127425114206294179575 19947191137671309441269363)
  ·
    refine ⟨29920786706506964161904045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19947191137671309441269363 29920786706506964161904045)
    ·
      refine ⟨11220295014940111560714017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29920786706506964161904045 11220295014940111560714017)
      ·
        refine ⟨8415221261205083670535513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11220295014940111560714017 8415221261205083670535513)
        ·
          refine ⟨6311415945903812752901635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8415221261205083670535513 6311415945903812752901635)
          ·
            refine ⟨9467123918855719129352453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311415945903812752901635 9467123918855719129352453)
            ·
              refine ⟨1775085734785447336753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9467123918855719129352453 1775085734785447336753585)
              ·
                refine ⟨1331314301089085502565189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1775085734785447336753585 1331314301089085502565189)
                ·
                  refine ⟨249621431454203531730973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331314301089085502565189 249621431454203531730973)
                  ·
                    rfl

theorem cell20_546903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_546903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546903 prefixEnd_546903 := by exact prefixLift 546903
  have htrace : WordTrace (prefixWord ++ tailWord_546903) baseStart_546903 baseEnd_546903 := by
    simpa [prefixWord, tailWord_546903, baseEnd_546903] using wordTrace_append hprefix tailTrace_546903
  have hstable : (prefixWord ++ tailWord_546903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546903).length < 2 ^ (prefixWord ++ tailWord_546903).sum := by decide
  have hdescent : baseEnd_546903 < baseStart_546903 := by decide
  rcases family_descends (prefixWord ++ tailWord_546903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546951 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_546951 : Nat := 118140960795 + 546951 * 2 ^ 59
def prefixEnd_546951 : Nat := 4983230072969 + 3 ^ 40 * 546951 * 2
def baseEnd_546951 : Nat := 249643339962128698130777

theorem tailTrace_546951 : CollatzResearch.WordTrace tailWord_546951 prefixEnd_546951 249643339962128698130777 := by
  unfold tailWord_546951
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948941841497413639016707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13299294560998275759344471 19948941841497413639016707)
  ·
    refine ⟨29923412762246120458525061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19948941841497413639016707 29923412762246120458525061)
    ·
      refine ⟨5610639892921147585973449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29923412762246120458525061 5610639892921147585973449)
      ·
        refine ⟨4207979919690860689480087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5610639892921147585973449 4207979919690860689480087)
        ·
          refine ⟨6311969879536291034220131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207979919690860689480087 6311969879536291034220131)
          ·
            refine ⟨9467954819304436551330197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311969879536291034220131 9467954819304436551330197)
            ·
              refine ⟨443810382154895463343603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9467954819304436551330197 443810382154895463343603)
              ·
                refine ⟨665715573232343195015405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443810382154895463343603 665715573232343195015405)
                ·
                  refine ⟨249643339962128698130777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665715573232343195015405 249643339962128698130777)
                  ·
                    rfl

theorem cell20_546951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_546951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546951 prefixEnd_546951 := by exact prefixLift 546951
  have htrace : WordTrace (prefixWord ++ tailWord_546951) baseStart_546951 baseEnd_546951 := by
    simpa [prefixWord, tailWord_546951, baseEnd_546951] using wordTrace_append hprefix tailTrace_546951
  have hstable : (prefixWord ++ tailWord_546951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546951).length < 2 ^ (prefixWord ++ tailWord_546951).sum := by decide
  have hdescent : baseEnd_546951 < baseStart_546951 := by decide
  rcases family_descends (prefixWord ++ tailWord_546951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546989 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_546989 : Nat := 118140960795 + 546989 * 2 ^ 59
def prefixEnd_546989 : Nat := 4983230072969 + 3 ^ 40 * 546989 * 2
def baseEnd_546989 : Nat := 249660684197569454863955

theorem tailTrace_546989 : CollatzResearch.WordTrace tailWord_546989 prefixEnd_546989 249660684197569454863955 := by
  unfold tailWord_546989
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950327815359746128900021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13300218543573164085933347 19950327815359746128900021)
  ·
    refine ⟨1870343232689976199584377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19950327815359746128900021 1870343232689976199584377)
    ·
      refine ⟨1402757424517482149688283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1870343232689976199584377 1402757424517482149688283)
      ·
        refine ⟨2104136136776223224532425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402757424517482149688283 2104136136776223224532425)
        ·
          refine ⟨1578102102582167418399319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104136136776223224532425 1578102102582167418399319)
          ·
            refine ⟨2367153153873251127598979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578102102582167418399319 2367153153873251127598979)
            ·
              refine ⟨3550729730809876691398469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367153153873251127598979 3550729730809876691398469)
              ·
                refine ⟨665761824526851879637213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3550729730809876691398469 665761824526851879637213)
                ·
                  refine ⟨249660684197569454863955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665761824526851879637213 249660684197569454863955)
                  ·
                    rfl

theorem cell20_546989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_546989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_546989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_546989 prefixEnd_546989 := by exact prefixLift 546989
  have htrace : WordTrace (prefixWord ++ tailWord_546989) baseStart_546989 baseEnd_546989 := by
    simpa [prefixWord, tailWord_546989, baseEnd_546989] using wordTrace_append hprefix tailTrace_546989
  have hstable : (prefixWord ++ tailWord_546989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546989).length < 2 ^ (prefixWord ++ tailWord_546989).sum := by decide
  have hdescent : baseEnd_546989 < baseStart_546989 := by decide
  rcases family_descends (prefixWord ++ tailWord_546989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547030 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_547030 : Nat := 118140960795 + 547030 * 2 ^ 59
def prefixEnd_547030 : Nat := 4983230072969 + 3 ^ 40 * 547030 * 2
def baseEnd_547030 : Nat := 249679397714755534497121

theorem tailTrace_547030 : CollatzResearch.WordTrace tailWord_547030 prefixEnd_547030 249679397714755534497121 := by
  unfold tailWord_547030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246988950513200633196409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13301215472140806754095029 1246988950513200633196409)
  ·
    refine ⟨935241712884900474897307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1246988950513200633196409 935241712884900474897307)
    ·
      refine ⟨1402862569327350712345961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935241712884900474897307 1402862569327350712345961)
      ·
        refine ⟨1052146926995513034259471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402862569327350712345961 1052146926995513034259471)
        ·
          refine ⟨1578220390493269551389207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052146926995513034259471 1578220390493269551389207)
          ·
            refine ⟨2367330585739904327083811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578220390493269551389207 2367330585739904327083811)
            ·
              refine ⟨3550995878609856490625717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367330585739904327083811 3550995878609856490625717)
              ·
                refine ⟨332905863619674045996161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3550995878609856490625717 332905863619674045996161)
                ·
                  refine ⟨249679397714755534497121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332905863619674045996161 249679397714755534497121)
                  ·
                    rfl

theorem cell20_547030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_547030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547030 prefixEnd_547030 := by exact prefixLift 547030
  have htrace : WordTrace (prefixWord ++ tailWord_547030) baseStart_547030 baseEnd_547030 := by
    simpa [prefixWord, tailWord_547030, baseEnd_547030] using wordTrace_append hprefix tailTrace_547030
  have hstable : (prefixWord ++ tailWord_547030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547030).length < 2 ^ (prefixWord ++ tailWord_547030).sum := by decide
  have hdescent : baseEnd_547030 < baseStart_547030 := by decide
  rcases family_descends (prefixWord ++ tailWord_547030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547031 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_547031 : Nat := 118140960795 + 547031 * 2 ^ 59
def prefixEnd_547031 : Nat := 4983230072969 + 3 ^ 40 * 547031 * 2
def baseEnd_547031 : Nat := 249679854142003975463783

theorem tailTrace_547031 : CollatzResearch.WordTrace tailWord_547031 prefixEnd_547031 249679854142003975463783 := by
  unfold tailWord_547031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19951859681207587301928947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13301239787471724867952631 19951859681207587301928947)
  ·
    refine ⟨29927789521811380952893421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19951859681207587301928947 29927789521811380952893421)
    ·
      refine ⟨11222921070679267857335033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29927789521811380952893421 11222921070679267857335033)
      ·
        refine ⟨8417190803009450893001275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11222921070679267857335033 8417190803009450893001275)
        ·
          refine ⟨12625786204514176339501913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8417190803009450893001275 12625786204514176339501913)
          ·
            refine ⟨9469339653385632254626435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625786204514176339501913 9469339653385632254626435)
            ·
              refine ⟨14204009480078448381939653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469339653385632254626435 14204009480078448381939653)
              ·
                refine ⟨2663251777514709071613685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14204009480078448381939653 2663251777514709071613685)
                ·
                  refine ⟨249679854142003975463783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663251777514709071613685 249679854142003975463783)
                  ·
                    rfl

theorem cell20_547031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_547031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547031 prefixEnd_547031 := by exact prefixLift 547031
  have htrace : WordTrace (prefixWord ++ tailWord_547031) baseStart_547031 baseEnd_547031 := by
    simpa [prefixWord, tailWord_547031, baseEnd_547031] using wordTrace_append hprefix tailTrace_547031
  have hstable : (prefixWord ++ tailWord_547031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547031).length < 2 ^ (prefixWord ++ tailWord_547031).sum := by decide
  have hdescent : baseEnd_547031 < baseStart_547031 := by decide
  rcases family_descends (prefixWord ++ tailWord_547031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547034 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_547034 : Nat := 118140960795 + 547034 * 2 ^ 59
def prefixEnd_547034 : Nat := 4983230072969 + 3 ^ 40 * 547034 * 2
def baseEnd_547034 : Nat := 249681223423749298363771

theorem tailTrace_547034 : CollatzResearch.WordTrace tailWord_547034 prefixEnd_547034 249681223423749298363771 := by
  unfold tailWord_547034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987992275049179703572039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13301312733464479209525437 4987992275049179703572039)
  ·
    refine ⟨7481988412573769555358059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4987992275049179703572039 7481988412573769555358059)
    ·
      refine ⟨11222982618860654333037089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481988412573769555358059 11222982618860654333037089)
      ·
        refine ⟨8417236964145490749777817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11222982618860654333037089 8417236964145490749777817)
        ·
          refine ⟨6312927723109118062333363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8417236964145490749777817 6312927723109118062333363)
          ·
            refine ⟨9469391584663677093500045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6312927723109118062333363 9469391584663677093500045)
            ·
              refine ⟨3551021844248878910062517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9469391584663677093500045 3551021844248878910062517)
              ·
                refine ⟨332908297898332397818361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3551021844248878910062517 332908297898332397818361)
                ·
                  refine ⟨249681223423749298363771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332908297898332397818361 249681223423749298363771)
                  ·
                    rfl

theorem cell20_547034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_547034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547034 prefixEnd_547034 := by exact prefixLift 547034
  have htrace : WordTrace (prefixWord ++ tailWord_547034) baseStart_547034 baseEnd_547034 := by
    simpa [prefixWord, tailWord_547034, baseEnd_547034] using wordTrace_append hprefix tailTrace_547034
  have hstable : (prefixWord ++ tailWord_547034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547034).length < 2 ^ (prefixWord ++ tailWord_547034).sum := by decide
  have hdescent : baseEnd_547034 < baseStart_547034 := by decide
  rcases family_descends (prefixWord ++ tailWord_547034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547048 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_547048 : Nat := 118140960795 + 547048 * 2 ^ 59
def prefixEnd_547048 : Nat := 4983230072969 + 3 ^ 40 * 547048 * 2
def baseEnd_547048 : Nat := 249687613405227471897047

theorem tailTrace_547048 : CollatzResearch.WordTrace tailWord_547048 prefixEnd_547048 249687613405227471897047 := by
  unfold tailWord_547048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976239861072999602648899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13301653148097332803531865 9976239861072999602648899)
  ·
    refine ⟨14964359791609499403973349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9976239861072999602648899 14964359791609499403973349)
    ·
      refine ⟨2805817460926781138245003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14964359791609499403973349 2805817460926781138245003)
      ·
        refine ⟨4208726191390171707367505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805817460926781138245003 4208726191390171707367505)
        ·
          refine ⟨3156544643542628780525629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4208726191390171707367505 3156544643542628780525629)
          ·
            refine ⟨1183704241328485792697111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3156544643542628780525629 1183704241328485792697111)
            ·
              refine ⟨1775556361992728689045667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183704241328485792697111 1775556361992728689045667)
              ·
                refine ⟨2663334542989093033568501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775556361992728689045667 2663334542989093033568501)
                ·
                  refine ⟨249687613405227471897047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663334542989093033568501 249687613405227471897047)
                  ·
                    rfl

theorem cell20_547048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_547048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547048 prefixEnd_547048 := by exact prefixLift 547048
  have htrace : WordTrace (prefixWord ++ tailWord_547048) baseStart_547048 baseEnd_547048 := by
    simpa [prefixWord, tailWord_547048, baseEnd_547048] using wordTrace_append hprefix tailTrace_547048
  have hstable : (prefixWord ++ tailWord_547048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547048).length < 2 ^ (prefixWord ++ tailWord_547048).sum := by decide
  have hdescent : baseEnd_547048 < baseStart_547048 := by decide
  rcases family_descends (prefixWord ++ tailWord_547048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547055 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_547055 : Nat := 118140960795 + 547055 * 2 ^ 59
def prefixEnd_547055 : Nat := 4983230072969 + 3 ^ 40 * 547055 * 2
def baseEnd_547055 : Nat := 249690808395966558663685

theorem tailTrace_547055 : CollatzResearch.WordTrace tailWord_547055 prefixEnd_547055 249690808395966558663685 := by
  unfold tailWord_547055
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952735033120639400802619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13301823355413759600535079 19952735033120639400802619)
  ·
    refine ⟨29929102549680959101203929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19952735033120639400802619 29929102549680959101203929)
    ·
      refine ⟨22446826912260719325902947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29929102549680959101203929 22446826912260719325902947)
      ·
        refine ⟨33670240368391078988854421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22446826912260719325902947 33670240368391078988854421)
        ·
          refine ⟨1578292517268331827602551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33670240368391078988854421 1578292517268331827602551)
          ·
            refine ⟨2367438775902497741403827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578292517268331827602551 2367438775902497741403827)
            ·
              refine ⟨3551158163853746612105741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367438775902497741403827 3551158163853746612105741)
              ·
                refine ⟨1331684311445154979539653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3551158163853746612105741 1331684311445154979539653)
                ·
                  refine ⟨249690808395966558663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1331684311445154979539653 249690808395966558663685)
                  ·
                    rfl

theorem cell20_547055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_547055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547055 prefixEnd_547055 := by exact prefixLift 547055
  have htrace : WordTrace (prefixWord ++ tailWord_547055) baseStart_547055 baseEnd_547055 := by
    simpa [prefixWord, tailWord_547055, baseEnd_547055] using wordTrace_append hprefix tailTrace_547055
  have hstable : (prefixWord ++ tailWord_547055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547055).length < 2 ^ (prefixWord ++ tailWord_547055).sum := by decide
  have hdescent : baseEnd_547055 < baseStart_547055 := by decide
  rcases family_descends (prefixWord ++ tailWord_547055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547089 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 2]
def baseStart_547089 : Nat := 118140960795 + 547089 * 2 ^ 59
def prefixEnd_547089 : Nat := 4983230072969 + 3 ^ 40 * 547089 * 2
def baseEnd_547089 : Nat := 249706326922413551530213

theorem tailTrace_547089 : CollatzResearch.WordTrace tailWord_547089 prefixEnd_547089 249706326922413551530213 := by
  unfold tailWord_547089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19953975114997463207540321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13302650076664975471693547 19953975114997463207540321)
  ·
    refine ⟨14965481336248097405655241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19953975114997463207540321 14965481336248097405655241)
    ·
      refine ⟨11224111002186073054241431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14965481336248097405655241 11224111002186073054241431)
      ·
        refine ⟨16836166503279109581362147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11224111002186073054241431 16836166503279109581362147)
        ·
          refine ⟨25254249754918664372043221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16836166503279109581362147 25254249754918664372043221)
          ·
            refine ⟨591896478630906196219763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25254249754918664372043221 591896478630906196219763)
            ·
              refine ⟨887844717946359294329645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591896478630906196219763 887844717946359294329645)
              ·
                refine ⟨332941769229884735373617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887844717946359294329645 332941769229884735373617)
                ·
                  refine ⟨249706326922413551530213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332941769229884735373617 249706326922413551530213)
                  ·
                    rfl

theorem cell20_547089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_547089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547089 prefixEnd_547089 := by exact prefixLift 547089
  have htrace : WordTrace (prefixWord ++ tailWord_547089) baseStart_547089 baseEnd_547089 := by
    simpa [prefixWord, tailWord_547089, baseEnd_547089] using wordTrace_append hprefix tailTrace_547089
  have hstable : (prefixWord ++ tailWord_547089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547089).length < 2 ^ (prefixWord ++ tailWord_547089).sum := by decide
  have hdescent : baseEnd_547089 < baseStart_547089 := by decide
  rcases family_descends (prefixWord ++ tailWord_547089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547106 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_547106 : Nat := 118140960795 + 547106 * 2 ^ 59
def prefixEnd_547106 : Nat := 4983230072969 + 3 ^ 40 * 547106 * 2
def baseEnd_547106 : Nat := 249714086185637047963477

theorem tailTrace_547106 : CollatzResearch.WordTrace tailWord_547106 prefixEnd_547106 249714086185637047963477 := by
  unfold tailWord_547106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988648788983968777727293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13303063437290583407272781 4988648788983968777727293)
  ·
    refine ⟨1870743295868988291647735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4988648788983968777727293 1870743295868988291647735)
    ·
      refine ⟨2806114943803482437471603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870743295868988291647735 2806114943803482437471603)
      ·
        refine ⟨4209172415705223656207405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806114943803482437471603 4209172415705223656207405)
        ·
          refine ⟨1578439655889458871077777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4209172415705223656207405 1578439655889458871077777)
          ·
            refine ⟨1183829741917094153308333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578439655889458871077777 1183829741917094153308333)
            ·
              refine ⟨443936153218910307490625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183829741917094153308333 443936153218910307490625)
              ·
                refine ⟨332952114914182730617969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443936153218910307490625 332952114914182730617969)
                ·
                  refine ⟨249714086185637047963477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332952114914182730617969 249714086185637047963477)
                  ·
                    rfl

theorem cell20_547106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_547106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547106 prefixEnd_547106 := by exact prefixLift 547106
  have htrace : WordTrace (prefixWord ++ tailWord_547106) baseStart_547106 baseEnd_547106 := by
    simpa [prefixWord, tailWord_547106, baseEnd_547106] using wordTrace_append hprefix tailTrace_547106
  have hstable : (prefixWord ++ tailWord_547106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547106).length < 2 ^ (prefixWord ++ tailWord_547106).sum := by decide
  have hdescent : baseEnd_547106 < baseStart_547106 := by decide
  rcases family_descends (prefixWord ++ tailWord_547106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547107 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_547107 : Nat := 118140960795 + 547107 * 2 ^ 59
def prefixEnd_547107 : Nat := 4983230072969 + 3 ^ 40 * 547107 * 2
def baseEnd_547107 : Nat := 249714542612885488930139

theorem tailTrace_547107 : CollatzResearch.WordTrace tailWord_547107 prefixEnd_547107 249714542612885488930139 := by
  unfold tailWord_547107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954631628932252281695575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13303087752621501521130383 19954631628932252281695575)
  ·
    refine ⟨29931947443398378422543363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19954631628932252281695575 29931947443398378422543363)
    ·
      refine ⟨44897921165097567633815045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29931947443398378422543363 44897921165097567633815045)
      ·
        refine ⟨8418360218455793931340321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44897921165097567633815045 8418360218455793931340321)
        ·
          refine ⟨6313770163841845448505241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8418360218455793931340321 6313770163841845448505241)
          ·
            refine ⟨4735327622881384086378931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6313770163841845448505241 4735327622881384086378931)
            ·
              refine ⟨7102991434322076129568397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735327622881384086378931 7102991434322076129568397)
              ·
                refine ⟨2663621787870778548588149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7102991434322076129568397 2663621787870778548588149)
                ·
                  refine ⟨249714542612885488930139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663621787870778548588149 249714542612885488930139)
                  ·
                    rfl

theorem cell20_547107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_547107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547107 prefixEnd_547107 := by exact prefixLift 547107
  have htrace : WordTrace (prefixWord ++ tailWord_547107) baseStart_547107 baseEnd_547107 := by
    simpa [prefixWord, tailWord_547107, baseEnd_547107] using wordTrace_append hprefix tailTrace_547107
  have hstable : (prefixWord ++ tailWord_547107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547107).length < 2 ^ (prefixWord ++ tailWord_547107).sum := by decide
  have hdescent : baseEnd_547107 < baseStart_547107 := by decide
  rcases family_descends (prefixWord ++ tailWord_547107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547148 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_547148 : Nat := 118140960795 + 547148 * 2 ^ 59
def prefixEnd_547148 : Nat := 4983230072969 + 3 ^ 40 * 547148 * 2
def baseEnd_547148 : Nat := 249733256130071568563305

theorem tailTrace_547148 : CollatzResearch.WordTrace tailWord_547148 prefixEnd_547148 249733256130071568563305 := by
  unfold tailWord_547148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978063510891858141969049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13304084681189144189292065 9978063510891858141969049)
  ·
    refine ⟨7483547633168893606476787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9978063510891858141969049 7483547633168893606476787)
    ·
      refine ⟨11225321449753340409715181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7483547633168893606476787 11225321449753340409715181)
      ·
        refine ⟨4209495543657502653643193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11225321449753340409715181 4209495543657502653643193)
        ·
          refine ⟨3157121657743126990232395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209495543657502653643193 3157121657743126990232395)
          ·
            refine ⟨4735682486614690485348593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157121657743126990232395 4735682486614690485348593)
            ·
              refine ⟨3551761864961017864011445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4735682486614690485348593 3551761864961017864011445)
              ·
                refine ⟨332977674840095424751073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3551761864961017864011445 332977674840095424751073)
                ·
                  refine ⟨249733256130071568563305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332977674840095424751073 249733256130071568563305)
                  ·
                    rfl

theorem cell20_547148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_547148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547148 prefixEnd_547148 := by exact prefixLift 547148
  have htrace : WordTrace (prefixWord ++ tailWord_547148) baseStart_547148 baseEnd_547148 := by
    simpa [prefixWord, tailWord_547148, baseEnd_547148] using wordTrace_append hprefix tailTrace_547148
  have hstable : (prefixWord ++ tailWord_547148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547148).length < 2 ^ (prefixWord ++ tailWord_547148).sum := by decide
  have hdescent : baseEnd_547148 < baseStart_547148 := by decide
  rcases family_descends (prefixWord ++ tailWord_547148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547203 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 2]
def baseStart_547203 : Nat := 118140960795 + 547203 * 2 ^ 59
def prefixEnd_547203 : Nat := 4983230072969 + 3 ^ 40 * 547203 * 2
def baseEnd_547203 : Nat := 249758359628735821729747

theorem tailTrace_547203 : CollatzResearch.WordTrace tailWord_547203 prefixEnd_547203 249758359628735821729747 := by
  unfold tailWord_547203
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958133036584460677190263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13305422024389640451460175 19958133036584460677190263)
  ·
    refine ⟨29937199554876691015785395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19958133036584460677190263 29937199554876691015785395)
    ·
      refine ⟨44905799332315036523678093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29937199554876691015785395 44905799332315036523678093)
      ·
        refine ⟨16839674749618138696379285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44905799332315036523678093 16839674749618138696379285)
        ·
          refine ⟨789359753888350251392779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16839674749618138696379285 789359753888350251392779)
          ·
            refine ⟨1184039630832525377089169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789359753888350251392779 1184039630832525377089169)
            ·
              refine ⟨888029723124394032816877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184039630832525377089169 888029723124394032816877)
              ·
                refine ⟨333011146171647762306329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888029723124394032816877 333011146171647762306329)
                ·
                  refine ⟨249758359628735821729747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333011146171647762306329 249758359628735821729747)
                  ·
                    rfl

theorem cell20_547203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2].length) (baseStart_547203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547203 prefixEnd_547203 := by exact prefixLift 547203
  have htrace : WordTrace (prefixWord ++ tailWord_547203) baseStart_547203 baseEnd_547203 := by
    simpa [prefixWord, tailWord_547203, baseEnd_547203] using wordTrace_append hprefix tailTrace_547203
  have hstable : (prefixWord ++ tailWord_547203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547203).length < 2 ^ (prefixWord ++ tailWord_547203).sum := by decide
  have hdescent : baseEnd_547203 < baseStart_547203 := by decide
  rcases family_descends (prefixWord ++ tailWord_547203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547224 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_547224 : Nat := 118140960795 + 547224 * 2 ^ 59
def prefixEnd_547224 : Nat := 4983230072969 + 3 ^ 40 * 547224 * 2
def baseEnd_547224 : Nat := 249767944600953082029661

theorem tailTrace_547224 : CollatzResearch.WordTrace tailWord_547224 prefixEnd_547224 249767944600953082029661 := by
  unfold tailWord_547224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979449484754190631852363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13305932646338920842469817 9979449484754190631852363)
  ·
    refine ⟨14969174227131285947778545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9979449484754190631852363 14969174227131285947778545)
    ·
      refine ⟨11226880670348464460833909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14969174227131285947778545 11226880670348464460833909)
      ·
        refine ⟨1052520062845168543203179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11226880670348464460833909 1052520062845168543203179)
        ·
          refine ⟨1578780094267752814804769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052520062845168543203179 1578780094267752814804769)
          ·
            refine ⟨1184085070700814611103577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578780094267752814804769 1184085070700814611103577)
            ·
              refine ⟨888063803025610958327683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184085070700814611103577 888063803025610958327683)
              ·
                refine ⟨1332095704538416437491525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888063803025610958327683 1332095704538416437491525)
                ·
                  refine ⟨249767944600953082029661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332095704538416437491525 249767944600953082029661)
                  ·
                    rfl

theorem cell20_547224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_547224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547224 prefixEnd_547224 := by exact prefixLift 547224
  have htrace : WordTrace (prefixWord ++ tailWord_547224) baseStart_547224 baseEnd_547224 := by
    simpa [prefixWord, tailWord_547224, baseEnd_547224] using wordTrace_append hprefix tailTrace_547224
  have hstable : (prefixWord ++ tailWord_547224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547224).length < 2 ^ (prefixWord ++ tailWord_547224).sum := by decide
  have hdescent : baseEnd_547224 < baseStart_547224 := by decide
  rcases family_descends (prefixWord ++ tailWord_547224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547265 : List Nat := [1, 2, 7, 1, 1, 2, 6]
def baseStart_547265 : Nat := 118140960795 + 547265 * 2 ^ 59
def prefixEnd_547265 : Nat := 4983230072969 + 3 ^ 40 * 547265 * 2
def baseEnd_547265 : Nat := 27754073124237684629203

theorem tailTrace_547265 : CollatzResearch.WordTrace tailWord_547265 prefixEnd_547265 27754073124237684629203 := by
  unfold tailWord_547265
  simp only [CollatzResearch.WordTrace]
  refine ⟨19960394362359845265947249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13306929574906563510631499 19960394362359845265947249)
  ·
    refine ⟨14970295771769883949460437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19960394362359845265947249 14970295771769883949460437)
    ·
      refine ⟨350866307150856655065479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14970295771769883949460437 350866307150856655065479)
      ·
        refine ⟨526299460726284982598219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350866307150856655065479 526299460726284982598219)
        ·
          refine ⟨789449191089427473897329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526299460726284982598219 789449191089427473897329)
          ·
            refine ⟨592086893317070605422997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789449191089427473897329 592086893317070605422997)
            ·
              refine ⟨27754073124237684629203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 592086893317070605422997 27754073124237684629203)
              ·
                rfl

theorem cell20_547265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_547265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547265 prefixEnd_547265 := by exact prefixLift 547265
  have htrace : WordTrace (prefixWord ++ tailWord_547265) baseStart_547265 baseEnd_547265 := by
    simpa [prefixWord, tailWord_547265, baseEnd_547265] using wordTrace_append hprefix tailTrace_547265
  have hstable : (prefixWord ++ tailWord_547265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547265).length < 2 ^ (prefixWord ++ tailWord_547265).sum := by decide
  have hdescent : baseEnd_547265 < baseStart_547265 := by decide
  rcases family_descends (prefixWord ++ tailWord_547265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547273 : List Nat := [1, 2, 1, 1, 2, 1, 12]
def baseStart_547273 : Nat := 118140960795 + 547273 * 2 ^ 59
def prefixEnd_547273 : Nat := 4983230072969 + 3 ^ 40 * 547273 * 2
def baseEnd_547273 : Nat := 27754478837347409932903

theorem tailTrace_547273 : CollatzResearch.WordTrace tailWord_547273 prefixEnd_547273 27754478837347409932903 := by
  unfold tailWord_547273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19960686146330862632238473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13307124097553908421492315 19960686146330862632238473)
  ·
    refine ⟨14970514609748146974178855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19960686146330862632238473 14970514609748146974178855)
    ·
      refine ⟨22455771914622220461268283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14970514609748146974178855 22455771914622220461268283)
      ·
        refine ⟨33683657871933330691902425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22455771914622220461268283 33683657871933330691902425)
        ·
          refine ⟨25262743403949998018926819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33683657871933330691902425 25262743403949998018926819)
          ·
            refine ⟨37894115105924997028390229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25262743403949998018926819 37894115105924997028390229)
            ·
              refine ⟨27754478837347409932903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37894115105924997028390229 27754478837347409932903)
              ·
                rfl

theorem cell20_547273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_547273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547273 prefixEnd_547273 := by exact prefixLift 547273
  have htrace : WordTrace (prefixWord ++ tailWord_547273) baseStart_547273 baseEnd_547273 := by
    simpa [prefixWord, tailWord_547273, baseEnd_547273] using wordTrace_append hprefix tailTrace_547273
  have hstable : (prefixWord ++ tailWord_547273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547273).length < 2 ^ (prefixWord ++ tailWord_547273).sum := by decide
  have hdescent : baseEnd_547273 < baseStart_547273 := by decide
  rcases family_descends (prefixWord ++ tailWord_547273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547290 : List Nat := [3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_547290 : Nat := 118140960795 + 547290 * 2 ^ 59
def prefixEnd_547290 : Nat := 4983230072969 + 3 ^ 40 * 547290 * 2
def baseEnd_547290 : Nat := 83266022933116728609797

theorem tailTrace_547290 : CollatzResearch.WordTrace tailWord_547290 prefixEnd_547290 83266022933116728609797 := by
  unfold tailWord_547290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990326546817318633901831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13307537458179516357071549 4990326546817318633901831)
  ·
    refine ⟨7485489820225977950852747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990326546817318633901831 7485489820225977950852747)
    ·
      refine ⟨11228234730338966926279121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7485489820225977950852747 11228234730338966926279121)
      ·
        refine ⟨8421176047754225194709341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11228234730338966926279121 8421176047754225194709341)
        ·
          refine ⟨3157941017907834448016003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8421176047754225194709341 3157941017907834448016003)
          ·
            refine ⟨4736911526861751672024005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157941017907834448016003 4736911526861751672024005)
            ·
              refine ⟨888170911286578438504501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4736911526861751672024005 888170911286578438504501)
              ·
                refine ⟨83266022933116728609797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888170911286578438504501 83266022933116728609797)
                ·
                  rfl

theorem cell20_547290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_547290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547290 prefixEnd_547290 := by exact prefixLift 547290
  have htrace : WordTrace (prefixWord ++ tailWord_547290) baseStart_547290 baseEnd_547290 := by
    simpa [prefixWord, tailWord_547290, baseEnd_547290] using wordTrace_append hprefix tailTrace_547290
  have hstable : (prefixWord ++ tailWord_547290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547290).length < 2 ^ (prefixWord ++ tailWord_547290).sum := by decide
  have hdescent : baseEnd_547290 < baseStart_547290 := by decide
  rcases family_descends (prefixWord ++ tailWord_547290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547330 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_547330 : Nat := 118140960795 + 547330 * 2 ^ 59
def prefixEnd_547330 : Nat := 4983230072969 + 3 ^ 40 * 547330 * 2
def baseEnd_547330 : Nat := 249816325889287824495895

theorem tailTrace_547330 : CollatzResearch.WordTrace tailWord_547330 prefixEnd_547330 249816325889287824495895 := by
  unfold tailWord_547330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990691276781090341765861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13308510071416240911375629 4990691276781090341765861)
  ·
    refine ⟨935754614396454439081099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4990691276781090341765861 935754614396454439081099)
    ·
      refine ⟨1403631921594681658621649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935754614396454439081099 1403631921594681658621649)
      ·
        refine ⟨1052723941196011243966237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1403631921594681658621649 1052723941196011243966237)
        ·
          refine ⟨394771477948504216487339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1052723941196011243966237 394771477948504216487339)
          ·
            refine ⟨592157216922756324731009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394771477948504216487339 592157216922756324731009)
            ·
              refine ⟨444117912692067243548257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592157216922756324731009 444117912692067243548257)
              ·
                refine ⟨333088434519050432661193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444117912692067243548257 333088434519050432661193)
                ·
                  refine ⟨249816325889287824495895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333088434519050432661193 249816325889287824495895)
                  ·
                    rfl

theorem cell20_547330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_547330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547330 prefixEnd_547330 := by exact prefixLift 547330
  have htrace : WordTrace (prefixWord ++ tailWord_547330) baseStart_547330 baseEnd_547330 := by
    simpa [prefixWord, tailWord_547330, baseEnd_547330] using wordTrace_append hprefix tailTrace_547330
  have hstable : (prefixWord ++ tailWord_547330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547330).length < 2 ^ (prefixWord ++ tailWord_547330).sum := by decide
  have hdescent : baseEnd_547330 < baseStart_547330 := by decide
  rcases family_descends (prefixWord ++ tailWord_547330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547338 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_547338 : Nat := 118140960795 + 547338 * 2 ^ 59
def prefixEnd_547338 : Nat := 4983230072969 + 3 ^ 40 * 547338 * 2
def baseEnd_547338 : Nat := 249819977307275352229195

theorem tailTrace_547338 : CollatzResearch.WordTrace tailWord_547338 prefixEnd_547338 249819977307275352229195 := by
  unfold tailWord_547338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990764222773844683338667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13308704594063585822236445 4990764222773844683338667)
  ·
    refine ⟨7486146334160767025008001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990764222773844683338667 7486146334160767025008001)
    ·
      refine ⟨5614609750620575268756001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7486146334160767025008001 5614609750620575268756001)
      ·
        refine ⟨4210957312965431451567001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5614609750620575268756001 4210957312965431451567001)
        ·
          refine ⟨3158217984724073588675251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4210957312965431451567001 3158217984724073588675251)
          ·
            refine ⟨4737326977086110383012877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158217984724073588675251 4737326977086110383012877)
            ·
              refine ⟨1776497616407291393629829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4737326977086110383012877 1776497616407291393629829)
              ·
                refine ⟨333093303076367136305593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1776497616407291393629829 333093303076367136305593)
                ·
                  refine ⟨249819977307275352229195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333093303076367136305593 249819977307275352229195)
                  ·
                    rfl

theorem cell20_547338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_547338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547338 prefixEnd_547338 := by exact prefixLift 547338
  have htrace : WordTrace (prefixWord ++ tailWord_547338) baseStart_547338 baseEnd_547338 := by
    simpa [prefixWord, tailWord_547338, baseEnd_547338] using wordTrace_append hprefix tailTrace_547338
  have hstable : (prefixWord ++ tailWord_547338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547338).length < 2 ^ (prefixWord ++ tailWord_547338).sum := by decide
  have hdescent : baseEnd_547338 < baseStart_547338 := by decide
  rcases family_descends (prefixWord ++ tailWord_547338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547341 : List Nat := [1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_547341 : Nat := 118140960795 + 547341 * 2 ^ 59
def prefixEnd_547341 : Nat := 4983230072969 + 3 ^ 40 * 547341 * 2
def baseEnd_547341 : Nat := 83273782196340225043061

theorem tailTrace_547341 : CollatzResearch.WordTrace tailWord_547341 prefixEnd_547341 83273782196340225043061 := by
  unfold tailWord_547341
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963166310084510245713877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13308777540056340163809251 19963166310084510245713877)
  ·
    refine ⟨467886710392605708883919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19963166310084510245713877 467886710392605708883919)
    ·
      refine ⟨701830065588908563325879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467886710392605708883919 701830065588908563325879)
      ·
        refine ⟨1052745098383362844988819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701830065588908563325879 1052745098383362844988819)
        ·
          refine ⟨1579117647575044267483229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052745098383362844988819 1579117647575044267483229)
          ·
            refine ⟨592169117840641600306211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1579117647575044267483229 592169117840641600306211)
            ·
              refine ⟨888253676760962400459317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592169117840641600306211 888253676760962400459317)
              ·
                refine ⟨83273782196340225043061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888253676760962400459317 83273782196340225043061)
                ·
                  rfl

theorem cell20_547341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_547341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547341 prefixEnd_547341 := by exact prefixLift 547341
  have htrace : WordTrace (prefixWord ++ tailWord_547341) baseStart_547341 baseEnd_547341 := by
    simpa [prefixWord, tailWord_547341, baseEnd_547341] using wordTrace_append hprefix tailTrace_547341
  have hstable : (prefixWord ++ tailWord_547341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547341).length < 2 ^ (prefixWord ++ tailWord_547341).sum := by decide
  have hdescent : baseEnd_547341 < baseStart_547341 := by decide
  rcases family_descends (prefixWord ++ tailWord_547341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547352 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_547352 : Nat := 118140960795 + 547352 * 2 ^ 59
def prefixEnd_547352 : Nat := 4983230072969 + 3 ^ 40 * 547352 * 2
def baseEnd_547352 : Nat := 249826367288753525762471

theorem tailTrace_547352 : CollatzResearch.WordTrace tailWord_547352 prefixEnd_547352 249826367288753525762471 := by
  unfold tailWord_547352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981783756522329562182155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13309045008696439416242873 9981783756522329562182155)
  ·
    refine ⟨14972675634783494343273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9981783756522329562182155 14972675634783494343273233)
    ·
      refine ⟨11229506726087620757454925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14972675634783494343273233 11229506726087620757454925)
      ·
        refine ⟨4211065022282857784045597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11229506726087620757454925 4211065022282857784045597)
        ·
          refine ⟨1579149383356071669017099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4211065022282857784045597 1579149383356071669017099)
          ·
            refine ⟨2368724075034107503525649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579149383356071669017099 2368724075034107503525649)
            ·
              refine ⟨1776543056275580627644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368724075034107503525649 1776543056275580627644237)
              ·
                refine ⟨666203646103342735366589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1776543056275580627644237 666203646103342735366589)
                ·
                  refine ⟨249826367288753525762471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666203646103342735366589 249826367288753525762471)
                  ·
                    rfl

theorem cell20_547352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_547352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547352 prefixEnd_547352 := by exact prefixLift 547352
  have htrace : WordTrace (prefixWord ++ tailWord_547352) baseStart_547352 baseEnd_547352 := by
    simpa [prefixWord, tailWord_547352, baseEnd_547352] using wordTrace_append hprefix tailTrace_547352
  have hstable : (prefixWord ++ tailWord_547352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547352).length < 2 ^ (prefixWord ++ tailWord_547352).sum := by decide
  have hdescent : baseEnd_547352 < baseStart_547352 := by decide
  rcases family_descends (prefixWord ++ tailWord_547352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547397 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_547397 : Nat := 118140960795 + 547397 * 2 ^ 59
def prefixEnd_547397 : Nat := 4983230072969 + 3 ^ 40 * 547397 * 2
def baseEnd_547397 : Nat := 249846906514933369262287

theorem tailTrace_547397 : CollatzResearch.WordTrace tailWord_547397 prefixEnd_547397 249846906514933369262287 := by
  unfold tailWord_547397
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965208797881631809752445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13310139198587754539834963 19965208797881631809752445)
  ·
    refine ⟨7486953299205611928657167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19965208797881631809752445 7486953299205611928657167)
    ·
      refine ⟨11230429948808417892985751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486953299205611928657167 11230429948808417892985751)
      ·
        refine ⟨16845644923212626839478627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11230429948808417892985751 16845644923212626839478627)
        ·
          refine ⟨25268467384818940259217941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16845644923212626839478627 25268467384818940259217941)
          ·
            refine ⟨1184459408663387824650841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25268467384818940259217941 1184459408663387824650841)
            ·
              refine ⟨888344556497540868488131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184459408663387824650841 888344556497540868488131)
              ·
                refine ⟨1332516834746311302732197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888344556497540868488131 1332516834746311302732197)
                ·
                  refine ⟨249846906514933369262287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1332516834746311302732197 249846906514933369262287)
                  ·
                    rfl

theorem cell20_547397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_547397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547397 prefixEnd_547397 := by exact prefixLift 547397
  have htrace : WordTrace (prefixWord ++ tailWord_547397) baseStart_547397 baseEnd_547397 := by
    simpa [prefixWord, tailWord_547397, baseEnd_547397] using wordTrace_append hprefix tailTrace_547397
  have hstable : (prefixWord ++ tailWord_547397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547397).length < 2 ^ (prefixWord ++ tailWord_547397).sum := by decide
  have hdescent : baseEnd_547397 < baseStart_547397 := by decide
  rcases family_descends (prefixWord ++ tailWord_547397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 2]
def baseStart_547435 : Nat := 118140960795 + 547435 * 2 ^ 59
def prefixEnd_547435 : Nat := 4983230072969 + 3 ^ 40 * 547435 * 2
def baseEnd_547435 : Nat := 249864250750374125995465

theorem tailTrace_547435 : CollatzResearch.WordTrace tailWord_547435 prefixEnd_547435 249864250750374125995465 := by
  unfold tailWord_547435
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966594771743964299635759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13311063181162642866423839 19966594771743964299635759)
  ·
    refine ⟨29949892157615946449453639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19966594771743964299635759 29949892157615946449453639)
    ·
      refine ⟨44924838236423919674180459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29949892157615946449453639 44924838236423919674180459)
      ·
        refine ⟨67387257354635879511270689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44924838236423919674180459 67387257354635879511270689)
        ·
          refine ⟨50540443015976909633453017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67387257354635879511270689 50540443015976909633453017)
          ·
            refine ⟨37905332261982682225089763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50540443015976909633453017 37905332261982682225089763)
            ·
              refine ⟨56857998392974023337634645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37905332261982682225089763 56857998392974023337634645)
              ·
                refine ⟨333152334333832167993953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 56857998392974023337634645 333152334333832167993953)
                ·
                  refine ⟨249864250750374125995465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333152334333832167993953 249864250750374125995465)
                  ·
                    rfl

theorem cell20_547435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 2].length) (baseStart_547435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547435 prefixEnd_547435 := by exact prefixLift 547435
  have htrace : WordTrace (prefixWord ++ tailWord_547435) baseStart_547435 baseEnd_547435 := by
    simpa [prefixWord, tailWord_547435, baseEnd_547435] using wordTrace_append hprefix tailTrace_547435
  have hstable : (prefixWord ++ tailWord_547435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547435).length < 2 ^ (prefixWord ++ tailWord_547435).sum := by decide
  have hdescent : baseEnd_547435 < baseStart_547435 := by decide
  rcases family_descends (prefixWord ++ tailWord_547435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547449 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_547449 : Nat := 118140960795 + 547449 * 2 ^ 59
def prefixEnd_547449 : Nat := 4983230072969 + 3 ^ 40 * 547449 * 2
def baseEnd_547449 : Nat := 249870640731852299528741

theorem tailTrace_547449 : CollatzResearch.WordTrace tailWord_547449 prefixEnd_547449 249870640731852299528741 := by
  unfold tailWord_547449
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967105393693244690645401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13311403595795496460430267 19967105393693244690645401)
  ·
    refine ⟨14975329045269933517984051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19967105393693244690645401 14975329045269933517984051)
    ·
      refine ⟨22462993567904900276976077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14975329045269933517984051 22462993567904900276976077)
      ·
        refine ⟨8423622587964337603866029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22462993567904900276976077 8423622587964337603866029)
        ·
          refine ⟨3158858470486626601449761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8423622587964337603866029 3158858470486626601449761)
          ·
            refine ⟨2369143852864969951087321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3158858470486626601449761 2369143852864969951087321)
            ·
              refine ⟨1776857889648727463315491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369143852864969951087321 1776857889648727463315491)
              ·
                refine ⟨2665286834473091194973237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776857889648727463315491 2665286834473091194973237)
                ·
                  refine ⟨249870640731852299528741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2665286834473091194973237 249870640731852299528741)
                  ·
                    rfl

theorem cell20_547449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_547449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547449 prefixEnd_547449 := by exact prefixLift 547449
  have htrace : WordTrace (prefixWord ++ tailWord_547449) baseStart_547449 baseEnd_547449 := by
    simpa [prefixWord, tailWord_547449, baseEnd_547449] using wordTrace_append hprefix tailTrace_547449
  have hstable : (prefixWord ++ tailWord_547449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547449).length < 2 ^ (prefixWord ++ tailWord_547449).sum := by decide
  have hdescent : baseEnd_547449 < baseStart_547449 := by decide
  rcases family_descends (prefixWord ++ tailWord_547449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547507 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 2]
def baseStart_547507 : Nat := 118140960795 + 547507 * 2 ^ 59
def prefixEnd_547507 : Nat := 4983230072969 + 3 ^ 40 * 547507 * 2
def baseEnd_547507 : Nat := 249897113512261875595171

theorem tailTrace_547507 : CollatzResearch.WordTrace tailWord_547507 prefixEnd_547507 249897113512261875595171 := by
  unfold tailWord_547507
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969220827483120596256775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13312813884988747064171183 19969220827483120596256775)
  ·
    refine ⟨29953831241224680894385163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19969220827483120596256775 29953831241224680894385163)
    ·
      refine ⟨44930746861837021341577745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29953831241224680894385163 44930746861837021341577745)
      ·
        refine ⟨33698060146377766006183309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44930746861837021341577745 33698060146377766006183309)
        ·
          refine ⟨12636772554891662252318741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33698060146377766006183309 12636772554891662252318741)
          ·
            refine ⟨592348713510546668077441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12636772554891662252318741 592348713510546668077441)
            ·
              refine ⟨444261535132910001058081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592348713510546668077441 444261535132910001058081)
              ·
                refine ⟨333196151349682500793561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444261535132910001058081 333196151349682500793561)
                ·
                  refine ⟨249897113512261875595171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333196151349682500793561 249897113512261875595171)
                  ·
                    rfl

theorem cell20_547507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 2].length) (baseStart_547507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547507 prefixEnd_547507 := by exact prefixLift 547507
  have htrace : WordTrace (prefixWord ++ tailWord_547507) baseStart_547507 baseEnd_547507 := by
    simpa [prefixWord, tailWord_547507, baseEnd_547507] using wordTrace_append hprefix tailTrace_547507
  have hstable : (prefixWord ++ tailWord_547507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547507).length < 2 ^ (prefixWord ++ tailWord_547507).sum := by decide
  have hdescent : baseEnd_547507 < baseStart_547507 := by decide
  rcases family_descends (prefixWord ++ tailWord_547507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547566 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_547566 : Nat := 118140960795 + 547566 * 2 ^ 59
def prefixEnd_547566 : Nat := 4983230072969 + 3 ^ 40 * 547566 * 2
def baseEnd_547566 : Nat := 249924042719919892628263

theorem tailTrace_547566 : CollatzResearch.WordTrace tailWord_547566 prefixEnd_547566 249924042719919892628263 := by
  unfold tailWord_547566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496421591783671709081819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13314248489512915781769701 2496421591783671709081819)
  ·
    refine ⟨3744632387675507563622729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496421591783671709081819 3744632387675507563622729)
    ·
      refine ⟨2808474290756630672717047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3744632387675507563622729 2808474290756630672717047)
      ·
        refine ⟨4212711436134946009075571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808474290756630672717047 4212711436134946009075571)
        ·
          refine ⟨6319067154202419013613357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212711436134946009075571 6319067154202419013613357)
          ·
            refine ⟨2369650182825907130105009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6319067154202419013613357 2369650182825907130105009)
            ·
              refine ⟨1777237637119430347578757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369650182825907130105009 1777237637119430347578757)
              ·
                refine ⟨333232056959893190171017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1777237637119430347578757 333232056959893190171017)
                ·
                  refine ⟨249924042719919892628263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333232056959893190171017 249924042719919892628263)
                  ·
                    rfl

theorem cell20_547566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_547566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547566 prefixEnd_547566 := by exact prefixLift 547566
  have htrace : WordTrace (prefixWord ++ tailWord_547566) baseStart_547566 baseEnd_547566 := by
    simpa [prefixWord, tailWord_547566, baseEnd_547566] using wordTrace_append hprefix tailTrace_547566
  have hstable : (prefixWord ++ tailWord_547566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547566).length < 2 ^ (prefixWord ++ tailWord_547566).sum := by decide
  have hdescent : baseEnd_547566 < baseStart_547566 := by decide
  rcases family_descends (prefixWord ++ tailWord_547566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547584 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_547584 : Nat := 118140960795 + 547584 * 2 ^ 59
def prefixEnd_547584 : Nat := 4983230072969 + 3 ^ 40 * 547584 * 2
def baseEnd_547584 : Nat := 249932258410391830028189

theorem tailTrace_547584 : CollatzResearch.WordTrace tailWord_547584 prefixEnd_547584 249932258410391830028189 := by
  unfold tailWord_547584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986014624102081373404903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13314686165469441831206537 9986014624102081373404903)
  ·
    refine ⟨14979021936153122060107355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986014624102081373404903 14979021936153122060107355)
    ·
      refine ⟨22468532904229683090161033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14979021936153122060107355 22468532904229683090161033)
      ·
        refine ⟨16851399678172262317620775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22468532904229683090161033 16851399678172262317620775)
        ·
          refine ⟨25277099517258393476431163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16851399678172262317620775 25277099517258393476431163)
          ·
            refine ⟨37915649275887590214646745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25277099517258393476431163 37915649275887590214646745)
            ·
              refine ⟨28436736956915692660985059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37915649275887590214646745 28436736956915692660985059)
              ·
                refine ⟨42655105435373538991477589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28436736956915692660985059 42655105435373538991477589)
                ·
                  refine ⟨249932258410391830028189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42655105435373538991477589 249932258410391830028189)
                  ·
                    rfl

theorem cell20_547584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_547584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547584 prefixEnd_547584 := by exact prefixLift 547584
  have htrace : WordTrace (prefixWord ++ tailWord_547584) baseStart_547584 baseEnd_547584 := by
    simpa [prefixWord, tailWord_547584, baseEnd_547584] using wordTrace_append hprefix tailTrace_547584
  have hstable : (prefixWord ++ tailWord_547584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547584).length < 2 ^ (prefixWord ++ tailWord_547584).sum := by decide
  have hdescent : baseEnd_547584 < baseStart_547584 := by decide
  rcases family_descends (prefixWord ++ tailWord_547584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547615 : List Nat := [1, 1, 2, 4, 2, 2, 8]
def baseStart_547615 : Nat := 118140960795 + 547615 * 2 ^ 59
def prefixEnd_547615 : Nat := 4983230072969 + 3 ^ 40 * 547615 * 2
def baseEnd_547615 : Nat := 27771823072788166666081

theorem tailTrace_547615 : CollatzResearch.WordTrace tailWord_547615 prefixEnd_547615 27771823072788166666081 := by
  unfold tailWord_547615
  simp only [CollatzResearch.WordTrace]
  refine ⟨19973159911091855041188299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315439940727903360792199 19973159911091855041188299)
  ·
    refine ⟨29959739866637782561782449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19973159911091855041188299 29959739866637782561782449)
    ·
      refine ⟨22469804899978336921336837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29959739866637782561782449 22469804899978336921336837)
      ·
        refine ⟨4213088418745938172750657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22469804899978336921336837 4213088418745938172750657)
        ·
          refine ⟨3159816314059453629562993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213088418745938172750657 3159816314059453629562993)
          ·
            refine ⟨2369862235544590222172245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159816314059453629562993 2369862235544590222172245)
            ·
              refine ⟨27771823072788166666081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2369862235544590222172245 27771823072788166666081)
              ·
                rfl

theorem cell20_547615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_547615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547615 prefixEnd_547615 := by exact prefixLift 547615
  have htrace : WordTrace (prefixWord ++ tailWord_547615) baseStart_547615 baseEnd_547615 := by
    simpa [prefixWord, tailWord_547615, baseEnd_547615] using wordTrace_append hprefix tailTrace_547615
  have hstable : (prefixWord ++ tailWord_547615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547615).length < 2 ^ (prefixWord ++ tailWord_547615).sum := by decide
  have hdescent : baseEnd_547615 < baseStart_547615 := by decide
  rcases family_descends (prefixWord ++ tailWord_547615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547635 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_547635 : Nat := 118140960795 + 547635 * 2 ^ 59
def prefixEnd_547635 : Nat := 4983230072969 + 3 ^ 40 * 547635 * 2
def baseEnd_547635 : Nat := 249955536200062319327981

theorem tailTrace_547635 : CollatzResearch.WordTrace tailWord_547635 prefixEnd_547635 249955536200062319327981 := by
  unfold tailWord_547635
  simp only [CollatzResearch.WordTrace]
  refine ⟨19973889371019398456916359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315926247346265637944239 19973889371019398456916359)
  ·
    refine ⟨29960834056529097685374539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19973889371019398456916359 29960834056529097685374539)
    ·
      refine ⟨44941251084793646528061809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29960834056529097685374539 44941251084793646528061809)
      ·
        refine ⟨33705938313595234896046357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44941251084793646528061809 33705938313595234896046357)
        ·
          refine ⟨1579965858449776635752173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33705938313595234896046357 1579965858449776635752173)
          ·
            refine ⟨592487196918666238407065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1579965858449776635752173 592487196918666238407065)
            ·
              refine ⟨444365397688999678805299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592487196918666238407065 444365397688999678805299)
              ·
                refine ⟨666548096533499518207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444365397688999678805299 666548096533499518207949)
                ·
                  refine ⟨249955536200062319327981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666548096533499518207949 249955536200062319327981)
                  ·
                    rfl

theorem cell20_547635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_547635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547635 prefixEnd_547635 := by exact prefixLift 547635
  have htrace : WordTrace (prefixWord ++ tailWord_547635) baseStart_547635 baseEnd_547635 := by
    simpa [prefixWord, tailWord_547635, baseEnd_547635] using wordTrace_append hprefix tailTrace_547635
  have hstable : (prefixWord ++ tailWord_547635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547635).length < 2 ^ (prefixWord ++ tailWord_547635).sum := by decide
  have hdescent : baseEnd_547635 < baseStart_547635 := by decide
  rcases family_descends (prefixWord ++ tailWord_547635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547639 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_547639 : Nat := 118140960795 + 547639 * 2 ^ 59
def prefixEnd_547639 : Nat := 4983230072969 + 3 ^ 40 * 547639 * 2
def baseEnd_547639 : Nat := 249957361909056083194631

theorem tailTrace_547639 : CollatzResearch.WordTrace tailWord_547639 prefixEnd_547639 249957361909056083194631 := by
  unfold tailWord_547639
  simp only [CollatzResearch.WordTrace]
  refine ⟨19974035263004907140061971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13316023508669938093374647 19974035263004907140061971)
  ·
    refine ⟨29961052894507360710092957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19974035263004907140061971 29961052894507360710092957)
    ·
      refine ⟨11235394835440260266284859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29961052894507360710092957 11235394835440260266284859)
      ·
        refine ⟨16853092253160390399427289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11235394835440260266284859 16853092253160390399427289)
        ·
          refine ⟨12639819189870292799570467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16853092253160390399427289 12639819189870292799570467)
          ·
            refine ⟨18959728784805439199355701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12639819189870292799570467 18959728784805439199355701)
            ·
              refine ⟨1777474573575509924939597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18959728784805439199355701 1777474573575509924939597)
              ·
                refine ⟨666552965090816221852349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777474573575509924939597 666552965090816221852349)
                ·
                  refine ⟨249957361909056083194631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666552965090816221852349 249957361909056083194631)
                  ·
                    rfl

theorem cell20_547639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_547639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547639 prefixEnd_547639 := by exact prefixLift 547639
  have htrace : WordTrace (prefixWord ++ tailWord_547639) baseStart_547639 baseEnd_547639 := by
    simpa [prefixWord, tailWord_547639, baseEnd_547639] using wordTrace_append hprefix tailTrace_547639
  have hstable : (prefixWord ++ tailWord_547639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547639).length < 2 ^ (prefixWord ++ tailWord_547639).sum := by decide
  have hdescent : baseEnd_547639 < baseStart_547639 := by decide
  rcases family_descends (prefixWord ++ tailWord_547639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547676 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_547676 : Nat := 118140960795 + 547676 * 2 ^ 59
def prefixEnd_547676 : Nat := 4983230072969 + 3 ^ 40 * 547676 * 2
def baseEnd_547676 : Nat := 249974249717248398961147

theorem tailTrace_547676 : CollatzResearch.WordTrace tailWord_547676 prefixEnd_547676 249974249717248398961147 := by
  unfold tailWord_547676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987692381935431229579441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13316923175913908306105921 9987692381935431229579441)
  ·
    refine ⟨7490769286451573422184581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9987692381935431229579441 7490769286451573422184581)
    ·
      refine ⟨1404519241209670016659609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7490769286451573422184581 1404519241209670016659609)
      ·
        refine ⟨1053389430907252512494707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1404519241209670016659609 1053389430907252512494707)
        ·
          refine ⟨1580084146360878768742061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053389430907252512494707 1580084146360878768742061)
          ·
            refine ⟨592531554885329538278273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1580084146360878768742061 592531554885329538278273)
            ·
              refine ⟨444398666163997153708705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592531554885329538278273 444398666163997153708705)
              ·
                refine ⟨333298999622997865281529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444398666163997153708705 333298999622997865281529)
                ·
                  refine ⟨249974249717248398961147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333298999622997865281529 249974249717248398961147)
                  ·
                    rfl

theorem cell20_547676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_547676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547676 prefixEnd_547676 := by exact prefixLift 547676
  have htrace : WordTrace (prefixWord ++ tailWord_547676) baseStart_547676 baseEnd_547676 := by
    simpa [prefixWord, tailWord_547676, baseEnd_547676] using wordTrace_append hprefix tailTrace_547676
  have hstable : (prefixWord ++ tailWord_547676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547676).length < 2 ^ (prefixWord ++ tailWord_547676).sum := by decide
  have hdescent : baseEnd_547676 < baseStart_547676 := by decide
  rcases family_descends (prefixWord ++ tailWord_547676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547691 : List Nat := [1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_547691 : Nat := 118140960795 + 547691 * 2 ^ 59
def prefixEnd_547691 : Nat := 4983230072969 + 3 ^ 40 * 547691 * 2
def baseEnd_547691 : Nat := 83327032041991671153695

theorem tailTrace_547691 : CollatzResearch.WordTrace tailWord_547691 prefixEnd_547691 83327032041991671153695 := by
  unfold tailWord_547691
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975931858816520020954927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13317287905877680013969951 19975931858816520020954927)
  ·
    refine ⟨29963897788224780031432391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19975931858816520020954927 29963897788224780031432391)
    ·
      refine ⟨44945846682337170047148587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29963897788224780031432391 44945846682337170047148587)
      ·
        refine ⟨67418770023505755070722881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44945846682337170047148587 67418770023505755070722881)
        ·
          refine ⟨50564077517629316303042161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67418770023505755070722881 50564077517629316303042161)
          ·
            refine ⟨37923058138221987227281621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50564077517629316303042161 37923058138221987227281621)
            ·
              refine ⟨888821675114577825639413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37923058138221987227281621 888821675114577825639413)
              ·
                refine ⟨83327032041991671153695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 888821675114577825639413 83327032041991671153695)
                ·
                  rfl

theorem cell20_547691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_547691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547691 prefixEnd_547691 := by exact prefixLift 547691
  have htrace : WordTrace (prefixWord ++ tailWord_547691) baseStart_547691 baseEnd_547691 := by
    simpa [prefixWord, tailWord_547691, baseEnd_547691] using wordTrace_append hprefix tailTrace_547691
  have hstable : (prefixWord ++ tailWord_547691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547691).length < 2 ^ (prefixWord ++ tailWord_547691).sum := by decide
  have hdescent : baseEnd_547691 < baseStart_547691 := by decide
  rcases family_descends (prefixWord ++ tailWord_547691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547701 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_547701 : Nat := 118140960795 + 547701 * 2 ^ 59
def prefixEnd_547701 : Nat := 4983230072969 + 3 ^ 40 * 547701 * 2
def baseEnd_547701 : Nat := 249985660398459423127711

theorem tailTrace_547701 : CollatzResearch.WordTrace tailWord_547701 prefixEnd_547701 249985660398459423127711 := by
  unfold tailWord_547701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19976296588780291728818957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13317531059186861152545971 19976296588780291728818957)
  ·
    refine ⟨7491111220792609398307109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19976296588780291728818957 7491111220792609398307109)
    ·
      refine ⟨1404583353898614262182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7491111220792609398307109 1404583353898614262182583)
      ·
        refine ⟨2106875030847921393273875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404583353898614262182583 2106875030847921393273875)
        ·
          refine ⟨3160312546271882089910813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106875030847921393273875 3160312546271882089910813)
          ·
            refine ⟨1185117204851955783716555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3160312546271882089910813 1185117204851955783716555)
            ·
              refine ⟨1777675807277933675574833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185117204851955783716555 1777675807277933675574833)
              ·
                refine ⟨1333256855458450256681125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777675807277933675574833 1333256855458450256681125)
                ·
                  refine ⟨249985660398459423127711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333256855458450256681125 249985660398459423127711)
                  ·
                    rfl

theorem cell20_547701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_547701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547701 prefixEnd_547701 := by exact prefixLift 547701
  have htrace : WordTrace (prefixWord ++ tailWord_547701) baseStart_547701 baseEnd_547701 := by
    simpa [prefixWord, tailWord_547701, baseEnd_547701] using wordTrace_append hprefix tailTrace_547701
  have hstable : (prefixWord ++ tailWord_547701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547701).length < 2 ^ (prefixWord ++ tailWord_547701).sum := by decide
  have hdescent : baseEnd_547701 < baseStart_547701 := by decide
  rcases family_descends (prefixWord ++ tailWord_547701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547773 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 2]
def baseStart_547773 : Nat := 118140960795 + 547773 * 2 ^ 59
def prefixEnd_547773 : Nat := 4983230072969 + 3 ^ 40 * 547773 * 2
def baseEnd_547773 : Nat := 250018523160347172727417

theorem tailTrace_547773 : CollatzResearch.WordTrace tailWord_547773 prefixEnd_547773 250018523160347172727417 := by
  unfold tailWord_547773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19978922644519448025439973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13319281763012965350293315 19978922644519448025439973)
  ·
    refine ⟨3746047995847396504769995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19978922644519448025439973 3746047995847396504769995)
    ·
      refine ⟨5619071993771094757154993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746047995847396504769995 5619071993771094757154993)
      ·
        refine ⟨4214303995328321067866245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5619071993771094757154993 4214303995328321067866245)
        ·
          refine ⟨790181999124060200224921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4214303995328321067866245 790181999124060200224921)
          ·
            refine ⟨592636499343045150168691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790181999124060200224921 592636499343045150168691)
            ·
              refine ⟨888954749014567725253037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592636499343045150168691 888954749014567725253037)
              ·
                refine ⟨333358030880462896969889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888954749014567725253037 333358030880462896969889)
                ·
                  refine ⟨250018523160347172727417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333358030880462896969889 250018523160347172727417)
                  ·
                    rfl

theorem cell20_547773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_547773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547773 prefixEnd_547773 := by exact prefixLift 547773
  have htrace : WordTrace (prefixWord ++ tailWord_547773) baseStart_547773 baseEnd_547773 := by
    simpa [prefixWord, tailWord_547773, baseEnd_547773] using wordTrace_append hprefix tailTrace_547773
  have hstable : (prefixWord ++ tailWord_547773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547773).length < 2 ^ (prefixWord ++ tailWord_547773).sum := by decide
  have hdescent : baseEnd_547773 < baseStart_547773 := by decide
  rcases family_descends (prefixWord ++ tailWord_547773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547780 : List Nat := [2, 3, 3, 3, 2, 1, 6]
def baseStart_547780 : Nat := 118140960795 + 547780 * 2 ^ 59
def prefixEnd_547780 : Nat := 4983230072969 + 3 ^ 40 * 547780 * 2
def baseEnd_547780 : Nat := 27780190905676251054895

theorem tailTrace_547780 : CollatzResearch.WordTrace tailWord_547780 prefixEnd_547780 27780190905676251054895 := by
  unfold tailWord_547780
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989588977747044110472397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13319451970329392147296529 9989588977747044110472397)
  ·
    refine ⟨3746095866655141541427149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9989588977747044110472397 3746095866655141541427149)
    ·
      refine ⟨1404785949995678078035181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3746095866655141541427149 1404785949995678078035181)
      ·
        refine ⟨526794731248379279263193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1404785949995678078035181 526794731248379279263193)
        ·
          refine ⟨395096048436284459447395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526794731248379279263193 395096048436284459447395)
          ·
            refine ⟨592644072654426689171093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395096048436284459447395 592644072654426689171093)
            ·
              refine ⟨27780190905676251054895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 592644072654426689171093 27780190905676251054895)
              ·
                rfl

theorem cell20_547780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_547780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547780 prefixEnd_547780 := by exact prefixLift 547780
  have htrace : WordTrace (prefixWord ++ tailWord_547780) baseStart_547780 baseEnd_547780 := by
    simpa [prefixWord, tailWord_547780, baseEnd_547780] using wordTrace_append hprefix tailTrace_547780
  have hstable : (prefixWord ++ tailWord_547780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547780).length < 2 ^ (prefixWord ++ tailWord_547780).sum := by decide
  have hdescent : baseEnd_547780 < baseStart_547780 := by decide
  rcases family_descends (prefixWord ++ tailWord_547780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547784 : List Nat := [2, 1, 3, 1, 5, 2, 6]
def baseStart_547784 : Nat := 118140960795 + 547784 * 2 ^ 59
def prefixEnd_547784 : Nat := 4983230072969 + 3 ^ 40 * 547784 * 2
def baseEnd_547784 : Nat := 27780393762231113706745

theorem tailTrace_547784 : CollatzResearch.WordTrace tailWord_547784 prefixEnd_547784 27780393762231113706745 := by
  unfold tailWord_547784
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989661923739798452045203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13319549231653064602726937 9989661923739798452045203)
  ·
    refine ⟨14984492885609697678067805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9989661923739798452045203 14984492885609697678067805)
    ·
      refine ⟨5619184832103636629275427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14984492885609697678067805 5619184832103636629275427)
      ·
        refine ⟨8428777248155454943913141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619184832103636629275427 8428777248155454943913141)
        ·
          refine ⟨790197867014573900991857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8428777248155454943913141 790197867014573900991857)
          ·
            refine ⟨592648400260930425743893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790197867014573900991857 592648400260930425743893)
            ·
              refine ⟨27780393762231113706745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 592648400260930425743893 27780393762231113706745)
              ·
                rfl

theorem cell20_547784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_547784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547784 prefixEnd_547784 := by exact prefixLift 547784
  have htrace : WordTrace (prefixWord ++ tailWord_547784) baseStart_547784 baseEnd_547784 := by
    simpa [prefixWord, tailWord_547784, baseEnd_547784] using wordTrace_append hprefix tailTrace_547784
  have hstable : (prefixWord ++ tailWord_547784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547784).length < 2 ^ (prefixWord ++ tailWord_547784).sum := by decide
  have hdescent : baseEnd_547784 < baseStart_547784 := by decide
  rcases family_descends (prefixWord ++ tailWord_547784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547794 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_547794 : Nat := 118140960795 + 547794 * 2 ^ 59
def prefixEnd_547794 : Nat := 4983230072969 + 3 ^ 40 * 547794 * 2
def baseEnd_547794 : Nat := 250028108132564433027331

theorem tailTrace_547794 : CollatzResearch.WordTrace tailWord_547794 prefixEnd_547794 250028108132564433027331 := by
  unfold tailWord_547794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994922144360842152988609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13319792384962245741302957 4994922144360842152988609)
  ·
    refine ⟨3746191608270631614741457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4994922144360842152988609 3746191608270631614741457)
    ·
      refine ⟨2809643706202973711056093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3746191608270631614741457 2809643706202973711056093)
      ·
        refine ⟨1053616389826115141646035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2809643706202973711056093 1053616389826115141646035)
        ·
          refine ⟨1580424584739172712469053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053616389826115141646035 1580424584739172712469053)
          ·
            refine ⟨592659219277189767175895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1580424584739172712469053 592659219277189767175895)
            ·
              refine ⟨888988828915784650763843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592659219277189767175895 888988828915784650763843)
              ·
                refine ⟨1333483243373676976145765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888988828915784650763843 1333483243373676976145765)
                ·
                  refine ⟨250028108132564433027331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333483243373676976145765 250028108132564433027331)
                  ·
                    rfl

theorem cell20_547794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_547794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547794 prefixEnd_547794 := by exact prefixLift 547794
  have htrace : WordTrace (prefixWord ++ tailWord_547794) baseStart_547794 baseEnd_547794 := by
    simpa [prefixWord, tailWord_547794, baseEnd_547794] using wordTrace_append hprefix tailTrace_547794
  have hstable : (prefixWord ++ tailWord_547794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547794).length < 2 ^ (prefixWord ++ tailWord_547794).sum := by decide
  have hdescent : baseEnd_547794 < baseStart_547794 := by decide
  rcases family_descends (prefixWord ++ tailWord_547794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547812 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_547812 : Nat := 118140960795 + 547812 * 2 ^ 59
def prefixEnd_547812 : Nat := 4983230072969 + 3 ^ 40 * 547812 * 2
def baseEnd_547812 : Nat := 250036323823036370427257

theorem tailTrace_547812 : CollatzResearch.WordTrace tailWord_547812 prefixEnd_547812 250036323823036370427257 := by
  unfold tailWord_547812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990172545689078843054845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13320230060918771790739793 9990172545689078843054845)
  ·
    refine ⟨3746314704633404566145567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9990172545689078843054845 3746314704633404566145567)
    ·
      refine ⟨5619472056950106849218351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746314704633404566145567 5619472056950106849218351)
      ·
        refine ⟨8429208085425160273827527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619472056950106849218351 8429208085425160273827527)
        ·
          refine ⟨12643812128137740410741291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429208085425160273827527 12643812128137740410741291)
          ·
            refine ⟨18965718192206610616111937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12643812128137740410741291 18965718192206610616111937)
            ·
              refine ⟨14224288644154957962083953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18965718192206610616111937 14224288644154957962083953)
              ·
                refine ⟨10668216483116218471562965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14224288644154957962083953 10668216483116218471562965)
                ·
                  refine ⟨250036323823036370427257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10668216483116218471562965 250036323823036370427257)
                  ·
                    rfl

theorem cell20_547812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_547812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547812 prefixEnd_547812 := by exact prefixLift 547812
  have htrace : WordTrace (prefixWord ++ tailWord_547812) baseStart_547812 baseEnd_547812 := by
    simpa [prefixWord, tailWord_547812, baseEnd_547812] using wordTrace_append hprefix tailTrace_547812
  have hstable : (prefixWord ++ tailWord_547812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547812).length < 2 ^ (prefixWord ++ tailWord_547812).sum := by decide
  have hdescent : baseEnd_547812 < baseStart_547812 := by decide
  rcases family_descends (prefixWord ++ tailWord_547812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547842 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_547842 : Nat := 118140960795 + 547842 * 2 ^ 59
def prefixEnd_547842 : Nat := 4983230072969 + 3 ^ 40 * 547842 * 2
def baseEnd_547842 : Nat := 250050016640489599427135

theorem tailTrace_547842 : CollatzResearch.WordTrace tailWord_547842 prefixEnd_547842 250050016640489599427135 := by
  unfold tailWord_547842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995359820317368202425445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13320959520846315206467853 4995359820317368202425445)
  ·
    refine ⟨936629966309506537954771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4995359820317368202425445 936629966309506537954771)
    ·
      refine ⟨1404944949464259806932157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936629966309506537954771 1404944949464259806932157)
      ·
        refine ⟨526854356049097427599559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1404944949464259806932157 526854356049097427599559)
        ·
          refine ⟨790281534073646141399339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526854356049097427599559 790281534073646141399339)
          ·
            refine ⟨1185422301110469212099009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790281534073646141399339 1185422301110469212099009)
            ·
              refine ⟨889066725832851909074257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185422301110469212099009 889066725832851909074257)
              ·
                refine ⟨666800044374638931805693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889066725832851909074257 666800044374638931805693)
                ·
                  refine ⟨250050016640489599427135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666800044374638931805693 250050016640489599427135)
                  ·
                    rfl

theorem cell20_547842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_547842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547842 prefixEnd_547842 := by exact prefixLift 547842
  have htrace : WordTrace (prefixWord ++ tailWord_547842) baseStart_547842 baseEnd_547842 := by
    simpa [prefixWord, tailWord_547842, baseEnd_547842] using wordTrace_append hprefix tailTrace_547842
  have hstable : (prefixWord ++ tailWord_547842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547842).length < 2 ^ (prefixWord ++ tailWord_547842).sum := by decide
  have hdescent : baseEnd_547842 < baseStart_547842 := by decide
  rcases family_descends (prefixWord ++ tailWord_547842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547857 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_547857 : Nat := 118140960795 + 547857 * 2 ^ 59
def prefixEnd_547857 : Nat := 4983230072969 + 3 ^ 40 * 547857 * 2
def baseEnd_547857 : Nat := 250056863049216213927073

theorem tailTrace_547857 : CollatzResearch.WordTrace tailWord_547857 prefixEnd_547857 250056863049216213927073 := by
  unfold tailWord_547857
  simp only [CollatzResearch.WordTrace]
  refine ⟨19981986376215130371497825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13321324250810086914331883 19981986376215130371497825)
  ·
    refine ⟨14986489782161347778623369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19981986376215130371497825 14986489782161347778623369)
    ·
      refine ⟨11239867336621010833967527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14986489782161347778623369 11239867336621010833967527)
      ·
        refine ⟨16859801004931516250951291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11239867336621010833967527 16859801004931516250951291)
        ·
          refine ⟨25289701507397274376426937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16859801004931516250951291 25289701507397274376426937)
          ·
            refine ⟨18967276130547955782320203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25289701507397274376426937 18967276130547955782320203)
            ·
              refine ⟨28450914195821933673480305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18967276130547955782320203 28450914195821933673480305)
              ·
                refine ⟨21338185646866450255110229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28450914195821933673480305 21338185646866450255110229)
                ·
                  refine ⟨250056863049216213927073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21338185646866450255110229 250056863049216213927073)
                  ·
                    rfl

theorem cell20_547857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_547857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547857 prefixEnd_547857 := by exact prefixLift 547857
  have htrace : WordTrace (prefixWord ++ tailWord_547857) baseStart_547857 baseEnd_547857 := by
    simpa [prefixWord, tailWord_547857, baseEnd_547857] using wordTrace_append hprefix tailTrace_547857
  have hstable : (prefixWord ++ tailWord_547857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547857).length < 2 ^ (prefixWord ++ tailWord_547857).sum := by decide
  have hdescent : baseEnd_547857 < baseStart_547857 := by decide
  rcases family_descends (prefixWord ++ tailWord_547857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547874 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_547874 : Nat := 118140960795 + 547874 * 2 ^ 59
def prefixEnd_547874 : Nat := 4983230072969 + 3 ^ 40 * 547874 * 2
def baseEnd_547874 : Nat := 250064622312439710360337

theorem tailTrace_547874 : CollatzResearch.WordTrace tailWord_547874 prefixEnd_547874 250064622312439710360337 := by
  unfold tailWord_547874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995651604288385568716669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13321737611435694849911117 4995651604288385568716669)
  ·
    refine ⟨1873369351608144588268751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4995651604288385568716669 1873369351608144588268751)
    ·
      refine ⟨2810054027412216882403127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873369351608144588268751 2810054027412216882403127)
      ·
        refine ⟨4215081041118325323604691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810054027412216882403127 4215081041118325323604691)
        ·
          refine ⟨6322621561677487985407037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215081041118325323604691 6322621561677487985407037)
          ·
            refine ⟨2370983085629057994527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6322621561677487985407037 2370983085629057994527639)
            ·
              refine ⟨3556474628443586991791459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370983085629057994527639 3556474628443586991791459)
              ·
                refine ⟨5334711942665380487687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556474628443586991791459 5334711942665380487687189)
                ·
                  refine ⟨250064622312439710360337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5334711942665380487687189 250064622312439710360337)
                  ·
                    rfl

theorem cell20_547874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_547874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547874 prefixEnd_547874 := by exact prefixLift 547874
  have htrace : WordTrace (prefixWord ++ tailWord_547874) baseStart_547874 baseEnd_547874 := by
    simpa [prefixWord, tailWord_547874, baseEnd_547874] using wordTrace_append hprefix tailTrace_547874
  have hstable : (prefixWord ++ tailWord_547874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547874).length < 2 ^ (prefixWord ++ tailWord_547874).sum := by decide
  have hdescent : baseEnd_547874 < baseStart_547874 := by decide
  rcases family_descends (prefixWord ++ tailWord_547874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547888 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_547888 : Nat := 118140960795 + 547888 * 2 ^ 59
def prefixEnd_547888 : Nat := 4983230072969 + 3 ^ 40 * 547888 * 2
def baseEnd_547888 : Nat := 250071012293917883893613

theorem tailTrace_547888 : CollatzResearch.WordTrace tailWord_547888 prefixEnd_547888 250071012293917883893613 := by
  unfold tailWord_547888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991558519551411332938159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13322078026068548443917545 9991558519551411332938159)
  ·
    refine ⟨14987337779327116999407239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9991558519551411332938159 14987337779327116999407239)
    ·
      refine ⟨22481006668990675499110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14987337779327116999407239 22481006668990675499110859)
      ·
        refine ⟨33721510003486013248666289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481006668990675499110859 33721510003486013248666289)
        ·
          refine ⟨25291132502614509936499717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33721510003486013248666289 25291132502614509936499717)
          ·
            refine ⟨4742087344240220613093697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25291132502614509936499717 4742087344240220613093697)
            ·
              refine ⟨3556565508180165459820273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742087344240220613093697 3556565508180165459820273)
              ·
                refine ⟨2667424131135124094865205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556565508180165459820273 2667424131135124094865205)
                ·
                  refine ⟨250071012293917883893613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667424131135124094865205 250071012293917883893613)
                  ·
                    rfl

theorem cell20_547888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_547888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547888 prefixEnd_547888 := by exact prefixLift 547888
  have htrace : WordTrace (prefixWord ++ tailWord_547888) baseStart_547888 baseEnd_547888 := by
    simpa [prefixWord, tailWord_547888, baseEnd_547888] using wordTrace_append hprefix tailTrace_547888
  have hstable : (prefixWord ++ tailWord_547888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547888).length < 2 ^ (prefixWord ++ tailWord_547888).sum := by decide
  have hdescent : baseEnd_547888 < baseStart_547888 := by decide
  rcases family_descends (prefixWord ++ tailWord_547888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547895 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_547895 : Nat := 118140960795 + 547895 * 2 ^ 59
def prefixEnd_547895 : Nat := 4983230072969 + 3 ^ 40 * 547895 * 2
def baseEnd_547895 : Nat := 250074207284656970660251

theorem tailTrace_547895 : CollatzResearch.WordTrace tailWord_547895 prefixEnd_547895 250074207284656970660251 := by
  unfold tailWord_547895
  simp only [CollatzResearch.WordTrace]
  refine ⟨19983372350077462861381139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13322248233384975240920759 19983372350077462861381139)
  ·
    refine ⟨29975058525116194292071709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19983372350077462861381139 29975058525116194292071709)
    ·
      refine ⟨11240646946918572859526891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29975058525116194292071709 11240646946918572859526891)
      ·
        refine ⟨16860970420377859289290337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11240646946918572859526891 16860970420377859289290337)
        ·
          refine ⟨12645727815283394466967753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16860970420377859289290337 12645727815283394466967753)
          ·
            refine ⟨9484295861462545850225815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12645727815283394466967753 9484295861462545850225815)
            ·
              refine ⟨14226443792193818775338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484295861462545850225815 14226443792193818775338723)
              ·
                refine ⟨21339665688290728163008085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14226443792193818775338723 21339665688290728163008085)
                ·
                  refine ⟨250074207284656970660251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21339665688290728163008085 250074207284656970660251)
                  ·
                    rfl

theorem cell20_547895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_547895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547895 prefixEnd_547895 := by exact prefixLift 547895
  have htrace : WordTrace (prefixWord ++ tailWord_547895) baseStart_547895 baseEnd_547895 := by
    simpa [prefixWord, tailWord_547895, baseEnd_547895] using wordTrace_append hprefix tailTrace_547895
  have hstable : (prefixWord ++ tailWord_547895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547895).length < 2 ^ (prefixWord ++ tailWord_547895).sum := by decide
  have hdescent : baseEnd_547895 < baseStart_547895 := by decide
  rcases family_descends (prefixWord ++ tailWord_547895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547912 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_547912 : Nat := 118140960795 + 547912 * 2 ^ 59
def prefixEnd_547912 : Nat := 4983230072969 + 3 ^ 40 * 547912 * 2
def baseEnd_547912 : Nat := 250081966547880467093515

theorem tailTrace_547912 : CollatzResearch.WordTrace tailWord_547912 prefixEnd_547912 250081966547880467093515 := by
  unfold tailWord_547912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991996195507937382374995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13322661594010583176499993 9991996195507937382374995)
  ·
    refine ⟨14987994293261906073562493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9991996195507937382374995 14987994293261906073562493)
    ·
      refine ⟨5620497859973214777585935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14987994293261906073562493 5620497859973214777585935)
      ·
        refine ⟨8430746789959822166378903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620497859973214777585935 8430746789959822166378903)
        ·
          refine ⟨12646120184939733249568355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430746789959822166378903 12646120184939733249568355)
          ·
            refine ⟨18969180277409599874352533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12646120184939733249568355 18969180277409599874352533)
            ·
              refine ⟨889180325503574994110275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18969180277409599874352533 889180325503574994110275)
              ·
                refine ⟨1333770488255362491165413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889180325503574994110275 1333770488255362491165413)
                ·
                  refine ⟨250081966547880467093515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1333770488255362491165413 250081966547880467093515)
                  ·
                    rfl

theorem cell20_547912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_547912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547912 prefixEnd_547912 := by exact prefixLift 547912
  have htrace : WordTrace (prefixWord ++ tailWord_547912) baseStart_547912 baseEnd_547912 := by
    simpa [prefixWord, tailWord_547912, baseEnd_547912] using wordTrace_append hprefix tailTrace_547912
  have hstable : (prefixWord ++ tailWord_547912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547912).length < 2 ^ (prefixWord ++ tailWord_547912).sum := by decide
  have hdescent : baseEnd_547912 < baseStart_547912 := by decide
  rcases family_descends (prefixWord ++ tailWord_547912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
