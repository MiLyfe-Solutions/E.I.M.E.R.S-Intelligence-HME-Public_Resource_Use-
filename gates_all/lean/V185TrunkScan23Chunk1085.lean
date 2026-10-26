import V185TrunkScan23Chunk1084

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6424366 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6424366 : Nat := 118140960795 + 6424366 * 2 ^ 59
def prefixEnd_6424366 : Nat := 4983230072969 + 3 ^ 40 * 6424366 * 2
def baseEnd_6424366 : Nat := 3298787658402516872179885

theorem tailTrace_6424366 : CollatzResearch.WordTrace tailWord_6424366 prefixEnd_6424366 3298787658402516872179885 := by
  unfold tailWord_6424366
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289484730453331400725619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156210585229084434137203301 29289484730453331400725619)
  ·
    refine ⟨43934227095679997101088429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29289484730453331400725619 43934227095679997101088429)
    ·
      refine ⟨16475335160879998912908161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43934227095679997101088429 16475335160879998912908161)
      ·
        refine ⟨12356501370659999184681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16475335160879998912908161 12356501370659999184681121)
        ·
          refine ⟨9267376027994999388510841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12356501370659999184681121 9267376027994999388510841)
          ·
            refine ⟨6950532020996249541383131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9267376027994999388510841 6950532020996249541383131)
            ·
              refine ⟨10425798031494374312074697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950532020996249541383131 10425798031494374312074697)
              ·
                refine ⟨7819348523620780734056023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10425798031494374312074697 7819348523620780734056023)
                ·
                  refine ⟨11729022785431171101084035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819348523620780734056023 11729022785431171101084035)
                  ·
                    refine ⟨17593534178146756651626053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11729022785431171101084035 17593534178146756651626053)
                    ·
                      refine ⟨3298787658402516872179885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17593534178146756651626053 3298787658402516872179885)
                      ·
                        rfl

theorem cell23_6424366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6424366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424366 prefixEnd_6424366 := by exact prefixLift 6424366
  have htrace : WordTrace (prefixWord ++ tailWord_6424366) baseStart_6424366 baseEnd_6424366 := by
    simpa [prefixWord, tailWord_6424366, baseEnd_6424366] using wordTrace_append hprefix tailTrace_6424366
  have hstable : (prefixWord ++ tailWord_6424366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424366).length < 2 ^ (prefixWord ++ tailWord_6424366).sum := by decide
  have hdescent : baseEnd_6424366 < baseStart_6424366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424369 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_6424369 : Nat := 118140960795 + 6424369 * 2 ^ 59
def prefixEnd_6424369 : Nat := 4983230072969 + 3 ^ 40 * 6424369 * 2
def baseEnd_6424369 : Nat := 3298789198844480360442371

theorem tailTrace_6424369 : CollatzResearch.WordTrace tailWord_6424369 prefixEnd_6424369 3298789198844480360442371 := by
  unfold tailWord_6424369
  simp only [CollatzResearch.WordTrace]
  refine ⟨234315987262615782718164161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156210658175077188478776107 234315987262615782718164161)
  ·
    refine ⟨175736990446961837038623121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234315987262615782718164161 175736990446961837038623121)
    ·
      refine ⟨131802742835221377778967341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175736990446961837038623121 131802742835221377778967341)
      ·
        refine ⟨49426028563208016667112753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131802742835221377778967341 49426028563208016667112753)
        ·
          refine ⟨37069521422406012500334565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49426028563208016667112753 37069521422406012500334565)
          ·
            refine ⟨6950535266701127343812731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37069521422406012500334565 6950535266701127343812731)
            ·
              refine ⟨10425802900051691015719097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950535266701127343812731 10425802900051691015719097)
              ·
                refine ⟨7819352175038768261789323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10425802900051691015719097 7819352175038768261789323)
                ·
                  refine ⟨11729028262558152392683985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819352175038768261789323 11729028262558152392683985)
                  ·
                    refine ⟨8796771196918614294512989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11729028262558152392683985 8796771196918614294512989)
                    ·
                      refine ⟨3298789198844480360442371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796771196918614294512989 3298789198844480360442371)
                      ·
                        rfl

theorem cell23_6424369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_6424369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424369 prefixEnd_6424369 := by exact prefixLift 6424369
  have htrace : WordTrace (prefixWord ++ tailWord_6424369) baseStart_6424369 baseEnd_6424369 := by
    simpa [prefixWord, tailWord_6424369, baseEnd_6424369] using wordTrace_append hprefix tailTrace_6424369
  have hstable : (prefixWord ++ tailWord_6424369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424369).length < 2 ^ (prefixWord ++ tailWord_6424369).sum := by decide
  have hdescent : baseEnd_6424369 < baseStart_6424369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424382 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_6424382 : Nat := 118140960795 + 6424382 * 2 ^ 59
def prefixEnd_6424382 : Nat := 4983230072969 + 3 ^ 40 * 6424382 * 2
def baseEnd_6424382 : Nat := 3298795874092988809579811

theorem tailTrace_6424382 : CollatzResearch.WordTrace tailWord_6424382 prefixEnd_6424382 3298795874092988809579811 := by
  unfold tailWord_6424382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289557676446085742298425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156210974274379123958924933 29289557676446085742298425)
  ·
    refine ⟨21967168257334564306723819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29289557676446085742298425 21967168257334564306723819)
    ·
      refine ⟨32950752386001846460085729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21967168257334564306723819 32950752386001846460085729)
      ·
        refine ⟨24713064289501384845064297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32950752386001846460085729 24713064289501384845064297)
        ·
          refine ⟨18534798217126038633798223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24713064289501384845064297 18534798217126038633798223)
          ·
            refine ⟨27802197325689057950697335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18534798217126038633798223 27802197325689057950697335)
            ·
              refine ⟨41703295988533586926046003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27802197325689057950697335 41703295988533586926046003)
              ·
                refine ⟨62554943982800380389069005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41703295988533586926046003 62554943982800380389069005)
                ·
                  refine ⟨23458103993550142645900877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62554943982800380389069005 23458103993550142645900877)
                  ·
                    refine ⟨8796788997581303492212829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23458103993550142645900877 8796788997581303492212829)
                    ·
                      refine ⟨3298795874092988809579811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796788997581303492212829 3298795874092988809579811)
                      ·
                        rfl

theorem cell23_6424382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_6424382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424382 prefixEnd_6424382 := by exact prefixLift 6424382
  have htrace : WordTrace (prefixWord ++ tailWord_6424382) baseStart_6424382 baseEnd_6424382 := by
    simpa [prefixWord, tailWord_6424382, baseEnd_6424382] using wordTrace_append hprefix tailTrace_6424382
  have hstable : (prefixWord ++ tailWord_6424382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424382).length < 2 ^ (prefixWord ++ tailWord_6424382).sum := by decide
  have hdescent : baseEnd_6424382 < baseStart_6424382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424405 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6424405 : Nat := 118140960795 + 6424405 * 2 ^ 59
def prefixEnd_6424405 : Nat := 4983230072969 + 3 ^ 40 * 6424405 * 2
def baseEnd_6424405 : Nat := 3298807684148042219592205

theorem tailTrace_6424405 : CollatzResearch.WordTrace tailWord_6424405 prefixEnd_6424405 3298807684148042219592205 := by
  unfold tailWord_6424405
  simp only [CollatzResearch.WordTrace]
  refine ⟨234317300290485360866474669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156211533526990240577649779 234317300290485360866474669)
  ·
    refine ⟨87868987608932010324928001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234317300290485360866474669 87868987608932010324928001)
    ·
      refine ⟨65901740706699007743696001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87868987608932010324928001 65901740706699007743696001)
      ·
        refine ⟨49426305530024255807772001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65901740706699007743696001 49426305530024255807772001)
        ·
          refine ⟨37069729147518191855829001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49426305530024255807772001 37069729147518191855829001)
          ·
            refine ⟨27802296860638643891871751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37069729147518191855829001 27802296860638643891871751)
            ·
              refine ⟨41703445290957965837807627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27802296860638643891871751 41703445290957965837807627)
              ·
                refine ⟨62555167936436948756711441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41703445290957965837807627 62555167936436948756711441)
                ·
                  refine ⟨46916375952327711567533581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62555167936436948756711441 46916375952327711567533581)
                  ·
                    refine ⟨17593640982122891837825093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46916375952327711567533581 17593640982122891837825093)
                    ·
                      refine ⟨3298807684148042219592205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17593640982122891837825093 3298807684148042219592205)
                      ·
                        rfl

theorem cell23_6424405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6424405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424405 prefixEnd_6424405 := by exact prefixLift 6424405
  have htrace : WordTrace (prefixWord ++ tailWord_6424405) baseStart_6424405 baseEnd_6424405 := by
    simpa [prefixWord, tailWord_6424405, baseEnd_6424405] using wordTrace_append hprefix tailTrace_6424405
  have hstable : (prefixWord ++ tailWord_6424405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424405).length < 2 ^ (prefixWord ++ tailWord_6424405).sum := by decide
  have hdescent : baseEnd_6424405 < baseStart_6424405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424415 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 6]
def baseStart_6424415 : Nat := 118140960795 + 6424415 * 2 ^ 59
def prefixEnd_6424415 : Nat := 4983230072969 + 3 ^ 40 * 6424415 * 2
def baseEnd_6424415 : Nat := 1099604272984862393489053

theorem tailTrace_6424415 : CollatzResearch.WordTrace tailWord_6424415 prefixEnd_6424415 1099604272984862393489053 := by
  unfold tailWord_6424415
  simp only [CollatzResearch.WordTrace]
  refine ⟨234317665020449132574338699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156211776680299421716225799 234317665020449132574338699)
  ·
    refine ⟨351476497530673698861508049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234317665020449132574338699 351476497530673698861508049)
    ·
      refine ⟨263607373148005274146131037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351476497530673698861508049 263607373148005274146131037)
      ·
        refine ⟨98852764930501977804799139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263607373148005274146131037 98852764930501977804799139)
        ·
          refine ⟨148279147395752966707198709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98852764930501977804799139 148279147395752966707198709)
          ·
            refine ⟨13901170068351840628799879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148279147395752966707198709 13901170068351840628799879)
            ·
              refine ⟨20851755102527760943199819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901170068351840628799879 20851755102527760943199819)
              ·
                refine ⟨31277632653791641414799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20851755102527760943199819 31277632653791641414799729)
                ·
                  refine ⟨23458224490343731061099797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31277632653791641414799729 23458224490343731061099797)
                  ·
                    refine ⟨1099604272984862393489053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23458224490343731061099797 1099604272984862393489053)
                    ·
                      rfl

theorem cell23_6424415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_6424415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424415 prefixEnd_6424415 := by exact prefixLift 6424415
  have htrace : WordTrace (prefixWord ++ tailWord_6424415) baseStart_6424415 baseEnd_6424415 := by
    simpa [prefixWord, tailWord_6424415, baseEnd_6424415] using wordTrace_append hprefix tailTrace_6424415
  have hstable : (prefixWord ++ tailWord_6424415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424415).length < 2 ^ (prefixWord ++ tailWord_6424415).sum := by decide
  have hdescent : baseEnd_6424415 < baseStart_6424415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424456 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6424456 : Nat := 118140960795 + 6424456 * 2 ^ 59
def prefixEnd_6424456 : Nat := 4983230072969 + 3 ^ 40 * 6424456 * 2
def baseEnd_6424456 : Nat := 3298833871661421520054471

theorem tailTrace_6424456 : CollatzResearch.WordTrace tailWord_6424456 prefixEnd_6424456 3298833871661421520054471 := by
  unfold tailWord_6424456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117159580206650298288290611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156212773608867064384387481 117159580206650298288290611)
  ·
    refine ⟨175739370309975447432435917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117159580206650298288290611 175739370309975447432435917)
    ·
      refine ⟨65902263866240792787163469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175739370309975447432435917 65902263866240792787163469)
      ·
        refine ⟨24713348949840297295186301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65902263866240792787163469 24713348949840297295186301)
        ·
          refine ⟨9267505856190111485694863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24713348949840297295186301 9267505856190111485694863)
          ·
            refine ⟨13901258784285167228542295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267505856190111485694863 13901258784285167228542295)
            ·
              refine ⟨20851888176427750842813443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901258784285167228542295 20851888176427750842813443)
              ·
                refine ⟨31277832264641626264220165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20851888176427750842813443 31277832264641626264220165)
                ·
                  refine ⟨5864593549620304924541281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31277832264641626264220165 5864593549620304924541281)
                  ·
                    refine ⟨4398445162215228693405961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5864593549620304924541281 4398445162215228693405961)
                    ·
                      refine ⟨3298833871661421520054471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398445162215228693405961 3298833871661421520054471)
                      ·
                        rfl

theorem cell23_6424456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6424456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424456 prefixEnd_6424456 := by exact prefixLift 6424456
  have htrace : WordTrace (prefixWord ++ tailWord_6424456) baseStart_6424456 baseEnd_6424456 := by
    simpa [prefixWord, tailWord_6424456, baseEnd_6424456] using wordTrace_append hprefix tailTrace_6424456
  have hstable : (prefixWord ++ tailWord_6424456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424456).length < 2 ^ (prefixWord ++ tailWord_6424456).sum := by decide
  have hdescent : baseEnd_6424456 < baseStart_6424456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424495 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_6424495 : Nat := 118140960795 + 6424495 * 2 ^ 59
def prefixEnd_6424495 : Nat := 4983230072969 + 3 ^ 40 * 6424495 * 2
def baseEnd_6424495 : Nat := 3298853897406946867466791

theorem tailTrace_6424495 : CollatzResearch.WordTrace tailWord_6424495 prefixEnd_6424495 3298853897406946867466791 := by
  unfold tailWord_6424495
  simp only [CollatzResearch.WordTrace]
  refine ⟨234320582860159306237250939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156213721906772870824833959 234320582860159306237250939)
  ·
    refine ⟨351480874290238959355876409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234320582860159306237250939 351480874290238959355876409)
    ·
      refine ⟨263610655717679219516907307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351480874290238959355876409 263610655717679219516907307)
      ·
        refine ⟨395415983576518829275360961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263610655717679219516907307 395415983576518829275360961)
        ·
          refine ⟨296561987682389121956520721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395415983576518829275360961 296561987682389121956520721)
          ·
            refine ⟨222421490761791841467390541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296561987682389121956520721 222421490761791841467390541)
            ·
              refine ⟨83408059035671940550271453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222421490761791841467390541 83408059035671940550271453)
              ·
                refine ⟨31278022138376977706351795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83408059035671940550271453 31278022138376977706351795)
                ·
                  refine ⟨46917033207565466559527693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31278022138376977706351795 46917033207565466559527693)
                  ·
                    refine ⟨17593887452837049959822885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46917033207565466559527693 17593887452837049959822885)
                    ·
                      refine ⟨3298853897406946867466791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17593887452837049959822885 3298853897406946867466791)
                      ·
                        rfl

theorem cell23_6424495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_6424495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424495 prefixEnd_6424495 := by exact prefixLift 6424495
  have htrace : WordTrace (prefixWord ++ tailWord_6424495) baseStart_6424495 baseEnd_6424495 := by
    simpa [prefixWord, tailWord_6424495, baseEnd_6424495] using wordTrace_append hprefix tailTrace_6424495
  have hstable : (prefixWord ++ tailWord_6424495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424495).length < 2 ^ (prefixWord ++ tailWord_6424495).sum := by decide
  have hdescent : baseEnd_6424495 < baseStart_6424495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424512 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_6424512 : Nat := 118140960795 + 6424512 * 2 ^ 59
def prefixEnd_6424512 : Nat := 4983230072969 + 3 ^ 40 * 6424512 * 2
def baseEnd_6424512 : Nat := 3298862626578073300954213

theorem tailTrace_6424512 : CollatzResearch.WordTrace tailWord_6424512 prefixEnd_6424512 3298862626578073300954213 := by
  unfold tailWord_6424512
  simp only [CollatzResearch.WordTrace]
  refine ⟨117160601450548859070309895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156214135267398478760413193 117160601450548859070309895)
  ·
    refine ⟨175740902175823288605464843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117160601450548859070309895 175740902175823288605464843)
    ·
      refine ⟨263611353263734932908197265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175740902175823288605464843 263611353263734932908197265)
      ·
        refine ⟨197708514947801199681147949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263611353263734932908197265 197708514947801199681147949)
        ·
          refine ⟨74140693105425449880430481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197708514947801199681147949 74140693105425449880430481)
          ·
            refine ⟨55605519829069087410322861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74140693105425449880430481 55605519829069087410322861)
            ·
              refine ⟨20852069935900907778871073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55605519829069087410322861 20852069935900907778871073)
              ·
                refine ⟨15639052451925680834153305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20852069935900907778871073 15639052451925680834153305)
                ·
                  refine ⟨11729289338944260625614979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15639052451925680834153305 11729289338944260625614979)
                  ·
                    refine ⟨17593934008416390938422469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11729289338944260625614979 17593934008416390938422469)
                    ·
                      refine ⟨3298862626578073300954213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17593934008416390938422469 3298862626578073300954213)
                      ·
                        rfl

theorem cell23_6424512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_6424512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424512 prefixEnd_6424512 := by exact prefixLift 6424512
  have htrace : WordTrace (prefixWord ++ tailWord_6424512) baseStart_6424512 baseEnd_6424512 := by
    simpa [prefixWord, tailWord_6424512, baseEnd_6424512] using wordTrace_append hprefix tailTrace_6424512
  have hstable : (prefixWord ++ tailWord_6424512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424512).length < 2 ^ (prefixWord ++ tailWord_6424512).sum := by decide
  have hdescent : baseEnd_6424512 < baseStart_6424512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424575 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_6424575 : Nat := 118140960795 + 6424575 * 2 ^ 59
def prefixEnd_6424575 : Nat := 4983230072969 + 3 ^ 40 * 6424575 * 2
def baseEnd_6424575 : Nat := 3298894975859306554466423

theorem tailTrace_6424575 : CollatzResearch.WordTrace tailWord_6424575 prefixEnd_6424575 3298894975859306554466423 := by
  unfold tailWord_6424575
  simp only [CollatzResearch.WordTrace]
  refine ⟨234323500699869479900163179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156215667133246319933442119 234323500699869479900163179)
  ·
    refine ⟨351485251049804219850244769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234323500699869479900163179 351485251049804219850244769)
    ·
      refine ⟨263613938287353164887683577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351485251049804219850244769 263613938287353164887683577)
      ·
        refine ⟨197710453715514873665762683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263613938287353164887683577 197710453715514873665762683)
        ·
          refine ⟨296565680573272310498644025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197710453715514873665762683 296565680573272310498644025)
          ·
            refine ⟨222424260429954232873983019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296565680573272310498644025 222424260429954232873983019)
            ·
              refine ⟨333636390644931349310974529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222424260429954232873983019 333636390644931349310974529)
              ·
                refine ⟨250227292983698511983230897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333636390644931349310974529 250227292983698511983230897)
                ·
                  refine ⟨187670469737773883987423173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250227292983698511983230897 187670469737773883987423173)
                  ·
                    refine ⟨35188213075832603247641845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187670469737773883987423173 35188213075832603247641845)
                    ·
                      refine ⟨3298894975859306554466423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35188213075832603247641845 3298894975859306554466423)
                      ·
                        rfl

theorem cell23_6424575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_6424575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424575 prefixEnd_6424575 := by exact prefixLift 6424575
  have htrace : WordTrace (prefixWord ++ tailWord_6424575) baseStart_6424575 baseEnd_6424575 := by
    simpa [prefixWord, tailWord_6424575, baseEnd_6424575] using wordTrace_append hprefix tailTrace_6424575
  have hstable : (prefixWord ++ tailWord_6424575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424575).length < 2 ^ (prefixWord ++ tailWord_6424575).sum := by decide
  have hdescent : baseEnd_6424575 < baseStart_6424575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424613 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_6424613 : Nat := 118140960795 + 6424613 * 2 ^ 59
def prefixEnd_6424613 : Nat := 4983230072969 + 3 ^ 40 * 6424613 * 2
def baseEnd_6424613 : Nat := 3298914488124177405791249

theorem tailTrace_6424613 : CollatzResearch.WordTrace tailWord_6424613 prefixEnd_6424613 3298914488124177405791249 := by
  unfold tailWord_6424613
  simp only [CollatzResearch.WordTrace]
  refine ⟨234324886673731812390046493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156216591115821208260030995 234324886673731812390046493)
  ·
    refine ⟨87871832502649429646267435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234324886673731812390046493 87871832502649429646267435)
    ·
      refine ⟨131807748753974144469401153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87871832502649429646267435 131807748753974144469401153)
      ·
        refine ⟨98855811565480608352050865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131807748753974144469401153 98855811565480608352050865)
        ·
          refine ⟨74141858674110456264038149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98855811565480608352050865 74141858674110456264038149)
          ·
            refine ⟨13901598501395710549507153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74141858674110456264038149 13901598501395710549507153)
            ·
              refine ⟨10426198876046782912130365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13901598501395710549507153 10426198876046782912130365)
              ·
                refine ⟨3909824578517543592048887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10426198876046782912130365 3909824578517543592048887)
                ·
                  refine ⟨5864736867776315388073331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909824578517543592048887 5864736867776315388073331)
                  ·
                    refine ⟨8797105301664473082109997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864736867776315388073331 8797105301664473082109997)
                    ·
                      refine ⟨3298914488124177405791249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797105301664473082109997 3298914488124177405791249)
                      ·
                        rfl

theorem cell23_6424613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_6424613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424613 prefixEnd_6424613 := by exact prefixLift 6424613
  have htrace : WordTrace (prefixWord ++ tailWord_6424613) baseStart_6424613 baseEnd_6424613 := by
    simpa [prefixWord, tailWord_6424613, baseEnd_6424613] using wordTrace_append hprefix tailTrace_6424613
  have hstable : (prefixWord ++ tailWord_6424613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424613).length < 2 ^ (prefixWord ++ tailWord_6424613).sum := by decide
  have hdescent : baseEnd_6424613 < baseStart_6424613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424653 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6424653 : Nat := 118140960795 + 6424653 * 2 ^ 59
def prefixEnd_6424653 : Nat := 4983230072969 + 3 ^ 40 * 6424653 * 2
def baseEnd_6424653 : Nat := 3298935027350357249291065

theorem tailTrace_6424653 : CollatzResearch.WordTrace tailWord_6424653 prefixEnd_6424653 3298935027350357249291065 := by
  unfold tailWord_6424653
  simp only [CollatzResearch.WordTrace]
  refine ⟨234326345593586899221502613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156217563729057932814335075 234326345593586899221502613)
  ·
    refine ⟨10984047449699385901007935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234326345593586899221502613 10984047449699385901007935)
    ·
      refine ⟨16476071174549078851511903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10984047449699385901007935 16476071174549078851511903)
      ·
        refine ⟨24714106761823618277267855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16476071174549078851511903 24714106761823618277267855)
        ·
          refine ⟨37071160142735427415901783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24714106761823618277267855 37071160142735427415901783)
          ·
            refine ⟨55606740214103141123852675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37071160142735427415901783 55606740214103141123852675)
            ·
              refine ⟨83410110321154711685779013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55606740214103141123852675 83410110321154711685779013)
              ·
                refine ⟨15639395685216508441083565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83410110321154711685779013 15639395685216508441083565)
                ·
                  refine ⟨5864773381956190665406337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15639395685216508441083565 5864773381956190665406337)
                  ·
                    refine ⟨4398580036467142999054753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5864773381956190665406337 4398580036467142999054753)
                    ·
                      refine ⟨3298935027350357249291065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398580036467142999054753 3298935027350357249291065)
                      ·
                        rfl

theorem cell23_6424653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6424653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424653 prefixEnd_6424653 := by exact prefixLift 6424653
  have htrace : WordTrace (prefixWord ++ tailWord_6424653) baseStart_6424653 baseEnd_6424653 := by
    simpa [prefixWord, tailWord_6424653, baseEnd_6424653] using wordTrace_append hprefix tailTrace_6424653
  have hstable : (prefixWord ++ tailWord_6424653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424653).length < 2 ^ (prefixWord ++ tailWord_6424653).sum := by decide
  have hdescent : baseEnd_6424653 < baseStart_6424653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424686 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6424686 : Nat := 118140960795 + 6424686 * 2 ^ 59
def prefixEnd_6424686 : Nat := 4983230072969 + 3 ^ 40 * 6424686 * 2
def baseEnd_6424686 : Nat := 3298951972211955620178413

theorem tailTrace_6424686 : CollatzResearch.WordTrace tailWord_6424686 prefixEnd_6424686 3298951972211955620178413 := by
  unfold tailWord_6424686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29290943650308418232181739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156218366134978230571635941 29290943650308418232181739)
  ·
    refine ⟨43936415475462627348272609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29290943650308418232181739 43936415475462627348272609)
    ·
      refine ⟨32952311606596970511204457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43936415475462627348272609 32952311606596970511204457)
      ·
        refine ⟨24714233704947727883403343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32952311606596970511204457 24714233704947727883403343)
        ·
          refine ⟨37071350557421591825105015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24714233704947727883403343 37071350557421591825105015)
          ·
            refine ⟨55607025836132387737657523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37071350557421591825105015 55607025836132387737657523)
            ·
              refine ⟨83410538754198581606486285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55607025836132387737657523 83410538754198581606486285)
              ·
                refine ⟨31278952032824468102432357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83410538754198581606486285 31278952032824468102432357)
                ·
                  refine ⟨5864803506154587769206067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31278952032824468102432357 5864803506154587769206067)
                  ·
                    refine ⟨8797205259231881653809101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864803506154587769206067 8797205259231881653809101)
                    ·
                      refine ⟨3298951972211955620178413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797205259231881653809101 3298951972211955620178413)
                      ·
                        rfl

theorem cell23_6424686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6424686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424686 prefixEnd_6424686 := by exact prefixLift 6424686
  have htrace : WordTrace (prefixWord ++ tailWord_6424686) baseStart_6424686 baseEnd_6424686 := by
    simpa [prefixWord, tailWord_6424686, baseEnd_6424686] using wordTrace_append hprefix tailTrace_6424686
  have hstable : (prefixWord ++ tailWord_6424686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424686).length < 2 ^ (prefixWord ++ tailWord_6424686).sum := by decide
  have hdescent : baseEnd_6424686 < baseStart_6424686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424759 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_6424759 : Nat := 118140960795 + 6424759 * 2 ^ 59
def prefixEnd_6424759 : Nat := 4983230072969 + 3 ^ 40 * 6424759 * 2
def baseEnd_6424759 : Nat := 3298989456299733834565577

theorem tailTrace_6424759 : CollatzResearch.WordTrace tailWord_6424759 prefixEnd_6424759 3298989456299733834565577 := by
  unfold tailWord_6424759
  simp only [CollatzResearch.WordTrace]
  refine ⟨234330211731202879324861331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156220141154135252883240887 234330211731202879324861331)
  ·
    refine ⟨351495317596804318987291997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234330211731202879324861331 351495317596804318987291997)
    ·
      refine ⟨131810744098801619620234499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351495317596804318987291997 131810744098801619620234499)
      ·
        refine ⟨197716116148202429430351749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131810744098801619620234499 197716116148202429430351749)
        ·
          refine ⟨37071771777787955518190953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197716116148202429430351749 37071771777787955518190953)
          ·
            refine ⟨27803828833340966638643215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37071771777787955518190953 27803828833340966638643215)
            ·
              refine ⟨41705743250011449957964823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27803828833340966638643215 41705743250011449957964823)
              ·
                refine ⟨62558614875017174936947235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41705743250011449957964823 62558614875017174936947235)
                ·
                  refine ⟨93837922312525762405420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62558614875017174936947235 93837922312525762405420853)
                  ·
                    refine ⟨8797305216799290225508205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93837922312525762405420853 8797305216799290225508205)
                    ·
                      refine ⟨3298989456299733834565577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797305216799290225508205 3298989456299733834565577)
                      ·
                        rfl

theorem cell23_6424759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_6424759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424759 prefixEnd_6424759 := by exact prefixLift 6424759
  have htrace : WordTrace (prefixWord ++ tailWord_6424759) baseStart_6424759 baseEnd_6424759 := by
    simpa [prefixWord, tailWord_6424759, baseEnd_6424759] using wordTrace_append hprefix tailTrace_6424759
  have hstable : (prefixWord ++ tailWord_6424759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424759).length < 2 ^ (prefixWord ++ tailWord_6424759).sum := by decide
  have hdescent : baseEnd_6424759 < baseStart_6424759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424766 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_6424766 : Nat := 118140960795 + 6424766 * 2 ^ 59
def prefixEnd_6424766 : Nat := 4983230072969 + 3 ^ 40 * 6424766 * 2
def baseEnd_6424766 : Nat := 366554783407146145242005

theorem tailTrace_6424766 : CollatzResearch.WordTrace tailWord_6424766 prefixEnd_6424766 366554783407146145242005 := by
  unfold tailWord_6424766
  simp only [CollatzResearch.WordTrace]
  refine ⟨29291308380272189940045769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156220311361451679680244101 29291308380272189940045769)
  ·
    refine ⟨21968481285204142455034327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29291308380272189940045769 21968481285204142455034327)
    ·
      refine ⟨32952721927806213682551491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21968481285204142455034327 32952721927806213682551491)
      ·
        refine ⟨49429082891709320523827237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32952721927806213682551491 49429082891709320523827237)
        ·
          refine ⟨9267953042195497598217607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49429082891709320523827237 9267953042195497598217607)
          ·
            refine ⟨13901929563293246397326411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267953042195497598217607 13901929563293246397326411)
            ·
              refine ⟨20852894344939869595989617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901929563293246397326411 20852894344939869595989617)
              ·
                refine ⟨15639670758704902196992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20852894344939869595989617 15639670758704902196992213)
                ·
                  refine ⟨366554783407146145242005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15639670758704902196992213 366554783407146145242005)
                  ·
                    rfl

theorem cell23_6424766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_6424766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424766 prefixEnd_6424766 := by exact prefixLift 6424766
  have htrace : WordTrace (prefixWord ++ tailWord_6424766) baseStart_6424766 baseEnd_6424766 := by
    simpa [prefixWord, tailWord_6424766, baseEnd_6424766] using wordTrace_append hprefix tailTrace_6424766
  have hstable : (prefixWord ++ tailWord_6424766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424766).length < 2 ^ (prefixWord ++ tailWord_6424766).sum := by decide
  have hdescent : baseEnd_6424766 < baseStart_6424766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424799 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_6424799 : Nat := 118140960795 + 6424799 * 2 ^ 59
def prefixEnd_6424799 : Nat := 4983230072969 + 3 ^ 40 * 6424799 * 2
def baseEnd_6424799 : Nat := 3299009995525913678065393

theorem tailTrace_6424799 : CollatzResearch.WordTrace tailWord_6424799 prefixEnd_6424799 3299009995525913678065393 := by
  unfold tailWord_6424799
  simp only [CollatzResearch.WordTrace]
  refine ⟨234331670651057966156317451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156221113767371977437544967 234331670651057966156317451)
  ·
    refine ⟨351497505976586949234476177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234331670651057966156317451 351497505976586949234476177)
    ·
      refine ⟨263623129482440211925857133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351497505976586949234476177 263623129482440211925857133)
      ·
        refine ⟨98858673555915079472196425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263623129482440211925857133 98858673555915079472196425)
        ·
          refine ⟨74144005166936309604147319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98858673555915079472196425 74144005166936309604147319)
          ·
            refine ⟨111216007750404464406220979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74144005166936309604147319 111216007750404464406220979)
            ·
              refine ⟨166824011625606696609331469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111216007750404464406220979 166824011625606696609331469)
              ·
                refine ⟨62559004359602511228499301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166824011625606696609331469 62559004359602511228499301)
                ·
                  refine ⟨11729813317425470855343619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62559004359602511228499301 11729813317425470855343619)
                  ·
                    refine ⟨17594719976138206283015429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11729813317425470855343619 17594719976138206283015429)
                    ·
                      refine ⟨3299009995525913678065393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17594719976138206283015429 3299009995525913678065393)
                      ·
                        rfl

theorem cell23_6424799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_6424799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424799 prefixEnd_6424799 := by exact prefixLift 6424799
  have htrace : WordTrace (prefixWord ++ tailWord_6424799) baseStart_6424799 baseEnd_6424799 := by
    simpa [prefixWord, tailWord_6424799, baseEnd_6424799] using wordTrace_append hprefix tailTrace_6424799
  have hstable : (prefixWord ++ tailWord_6424799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424799).length < 2 ^ (prefixWord ++ tailWord_6424799).sum := by decide
  have hdescent : baseEnd_6424799 < baseStart_6424799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424809 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_6424809 : Nat := 118140960795 + 6424809 * 2 ^ 59
def prefixEnd_6424809 : Nat := 4983230072969 + 3 ^ 40 * 6424809 * 2
def baseEnd_6424809 : Nat := 1099671710110819546313449

theorem tailTrace_6424809 : CollatzResearch.WordTrace tailWord_6424809 prefixEnd_6424809 1099671710110819546313449 := by
  unfold tailWord_6424809
  simp only [CollatzResearch.WordTrace]
  refine ⟨234332035381021737864181481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156221356920681158576120987 234332035381021737864181481)
  ·
    refine ⟨175749026535766303398136111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234332035381021737864181481 175749026535766303398136111)
    ·
      refine ⟨263623539803649455097204167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175749026535766303398136111 263623539803649455097204167)
      ·
        refine ⟨395435309705474182645806251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263623539803649455097204167 395435309705474182645806251)
        ·
          refine ⟨593152964558211273968709377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395435309705474182645806251 593152964558211273968709377)
          ·
            refine ⟨444864723418658455476532033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593152964558211273968709377 444864723418658455476532033)
            ·
              refine ⟨333648542563993841607399025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444864723418658455476532033 333648542563993841607399025)
              ·
                refine ⟨250236406922995381205549269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333648542563993841607399025 250236406922995381205549269)
                ·
                  refine ⟨5864915787257704247005061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250236406922995381205549269 5864915787257704247005061)
                  ·
                    refine ⟨1099671710110819546313449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864915787257704247005061 1099671710110819546313449)
                    ·
                      rfl

theorem cell23_6424809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_6424809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424809 prefixEnd_6424809 := by exact prefixLift 6424809
  have htrace : WordTrace (prefixWord ++ tailWord_6424809) baseStart_6424809 baseEnd_6424809 := by
    simpa [prefixWord, tailWord_6424809, baseEnd_6424809] using wordTrace_append hprefix tailTrace_6424809
  have hstable : (prefixWord ++ tailWord_6424809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424809).length < 2 ^ (prefixWord ++ tailWord_6424809).sum := by decide
  have hdescent : baseEnd_6424809 < baseStart_6424809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424819 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3]
def baseStart_6424819 : Nat := 118140960795 + 6424819 * 2 ^ 59
def prefixEnd_6424819 : Nat := 4983230072969 + 3 ^ 40 * 6424819 * 2
def baseEnd_6424819 : Nat := 3299020265139003599815301

theorem tailTrace_6424819 : CollatzResearch.WordTrace tailWord_6424819 prefixEnd_6424819 3299020265139003599815301 := by
  unfold tailWord_6424819
  simp only [CollatzResearch.WordTrace]
  refine ⟨234332400110985509572045511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156221600073990339714697007 234332400110985509572045511)
  ·
    refine ⟨351498600166478264358068267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234332400110985509572045511 351498600166478264358068267)
    ·
      refine ⟨527247900249717396537102401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351498600166478264358068267 527247900249717396537102401)
      ·
        refine ⟨395435925187288047402826801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527247900249717396537102401 395435925187288047402826801)
        ·
          refine ⟨296576943890466035552120101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395435925187288047402826801 296576943890466035552120101)
          ·
            refine ⟨55608176979462381666022519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296576943890466035552120101 55608176979462381666022519)
            ·
              refine ⟨83412265469193572499033779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55608176979462381666022519 83412265469193572499033779)
              ·
                refine ⟨125118398203790358748550669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83412265469193572499033779 125118398203790358748550669)
                ·
                  refine ⟨46919399326421384530706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125118398203790358748550669 46919399326421384530706501)
                  ·
                    refine ⟨8797387373704009599507469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46919399326421384530706501 8797387373704009599507469)
                    ·
                      refine ⟨3299020265139003599815301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797387373704009599507469 3299020265139003599815301)
                      ·
                        rfl

theorem cell23_6424819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_6424819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424819 prefixEnd_6424819 := by exact prefixLift 6424819
  have htrace : WordTrace (prefixWord ++ tailWord_6424819) baseStart_6424819 baseEnd_6424819 := by
    simpa [prefixWord, tailWord_6424819, baseEnd_6424819] using wordTrace_append hprefix tailTrace_6424819
  have hstable : (prefixWord ++ tailWord_6424819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424819).length < 2 ^ (prefixWord ++ tailWord_6424819).sum := by decide
  have hdescent : baseEnd_6424819 < baseStart_6424819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424826 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_6424826 : Nat := 118140960795 + 6424826 * 2 ^ 59
def prefixEnd_6424826 : Nat := 4983230072969 + 3 ^ 40 * 6424826 * 2
def baseEnd_6424826 : Nat := 1099674619834528357475923

theorem tailTrace_6424826 : CollatzResearch.WordTrace tailWord_6424826 prefixEnd_6424826 1099674619834528357475923 := by
  unfold tailWord_6424826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58583163855490037441887583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156221770281306766511700221 58583163855490037441887583)
  ·
    refine ⟨87874745783235056162831375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58583163855490037441887583 87874745783235056162831375)
    ·
      refine ⟨131812118674852584244247063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87874745783235056162831375 131812118674852584244247063)
      ·
        refine ⟨197718178012278876366370595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131812118674852584244247063 197718178012278876366370595)
        ·
          refine ⟨296577267018418314549555893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197718178012278876366370595 296577267018418314549555893)
          ·
            refine ⟨27804118782976716989020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296577267018418314549555893 27804118782976716989020865)
            ·
              refine ⟨20853089087232537741765649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27804118782976716989020865 20853089087232537741765649)
              ·
                refine ⟨15639816815424403306324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20853089087232537741765649 15639816815424403306324237)
                ·
                  refine ⟨5864931305784151239871589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15639816815424403306324237 5864931305784151239871589)
                  ·
                    refine ⟨1099674619834528357475923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864931305784151239871589 1099674619834528357475923)
                    ·
                      rfl

theorem cell23_6424826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_6424826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424826 prefixEnd_6424826 := by exact prefixLift 6424826
  have htrace : WordTrace (prefixWord ++ tailWord_6424826) baseStart_6424826 baseEnd_6424826 := by
    simpa [prefixWord, tailWord_6424826, baseEnd_6424826] using wordTrace_append hprefix tailTrace_6424826
  have hstable : (prefixWord ++ tailWord_6424826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424826).length < 2 ^ (prefixWord ++ tailWord_6424826).sum := by decide
  have hdescent : baseEnd_6424826 < baseStart_6424826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424876 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_6424876 : Nat := 118140960795 + 6424876 * 2 ^ 59
def prefixEnd_6424876 : Nat := 4983230072969 + 3 ^ 40 * 6424876 * 2
def baseEnd_6424876 : Nat := 3299049533536309876802539

theorem tailTrace_6424876 : CollatzResearch.WordTrace tailWord_6424876 prefixEnd_6424876 3299049533536309876802539 := by
  unfold tailWord_6424876
  simp only [CollatzResearch.WordTrace]
  refine ⟨117167239535889504153435241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156222986047852672204580321 117167239535889504153435241)
  ·
    refine ⟨87875429651917128115076431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117167239535889504153435241 87875429651917128115076431)
    ·
      refine ⟨131813144477875692172614647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87875429651917128115076431 131813144477875692172614647)
      ·
        refine ⟨197719716716813538258921971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131813144477875692172614647 197719716716813538258921971)
        ·
          refine ⟨296579575075220307388382957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197719716716813538258921971 296579575075220307388382957)
          ·
            refine ⟨111217340653207615270643609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296579575075220307388382957 111217340653207615270643609)
            ·
              refine ⟨83413005489905711452982707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111217340653207615270643609 83413005489905711452982707)
              ·
                refine ⟨125119508234858567179474061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83413005489905711452982707 125119508234858567179474061)
                ·
                  refine ⟨46919815588071962692302773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125119508234858567179474061 46919815588071962692302773)
                  ·
                    refine ⟨4398732711381746502403385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46919815588071962692302773 4398732711381746502403385)
                    ·
                      refine ⟨3299049533536309876802539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398732711381746502403385 3299049533536309876802539)
                      ·
                        rfl

theorem cell23_6424876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_6424876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424876 prefixEnd_6424876 := by exact prefixLift 6424876
  have htrace : WordTrace (prefixWord ++ tailWord_6424876) baseStart_6424876 baseEnd_6424876 := by
    simpa [prefixWord, tailWord_6424876, baseEnd_6424876] using wordTrace_append hprefix tailTrace_6424876
  have hstable : (prefixWord ++ tailWord_6424876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424876).length < 2 ^ (prefixWord ++ tailWord_6424876).sum := by decide
  have hdescent : baseEnd_6424876 < baseStart_6424876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424899 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 6]
def baseStart_6424899 : Nat := 118140960795 + 6424899 * 2 ^ 59
def prefixEnd_6424899 : Nat := 4983230072969 + 3 ^ 40 * 6424899 * 2
def baseEnd_6424899 : Nat := 1099687114530454428938311

theorem tailTrace_6424899 : CollatzResearch.WordTrace tailWord_6424899 prefixEnd_6424899 1099687114530454428938311 := by
  unfold tailWord_6424899
  simp only [CollatzResearch.WordTrace]
  refine ⟨234335317950695683234957751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156223545300463788823305167 234335317950695683234957751)
  ·
    refine ⟨351502976926043524852436627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234335317950695683234957751 351502976926043524852436627)
    ·
      refine ⟨527254465389065287278654941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351502976926043524852436627 527254465389065287278654941)
      ·
        refine ⟨197720424520899482729495603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527254465389065287278654941 197720424520899482729495603)
        ·
          refine ⟨296580636781349224094243405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197720424520899482729495603 296580636781349224094243405)
          ·
            refine ⟨111217738793005959035341277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296580636781349224094243405 111217738793005959035341277)
            ·
              refine ⟨41706652047377234638252979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111217738793005959035341277 41706652047377234638252979)
              ·
                refine ⟨62559978071065851957379469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41706652047377234638252979 62559978071065851957379469)
                ·
                  refine ⟨23459991776649694484017301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62559978071065851957379469 23459991776649694484017301)
                  ·
                    refine ⟨1099687114530454428938311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23459991776649694484017301 1099687114530454428938311)
                    ·
                      rfl

theorem cell23_6424899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_6424899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424899 prefixEnd_6424899 := by exact prefixLift 6424899
  have htrace : WordTrace (prefixWord ++ tailWord_6424899) baseStart_6424899 baseEnd_6424899 := by
    simpa [prefixWord, tailWord_6424899, baseEnd_6424899] using wordTrace_append hprefix tailTrace_6424899
  have hstable : (prefixWord ++ tailWord_6424899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424899).length < 2 ^ (prefixWord ++ tailWord_6424899).sum := by decide
  have hdescent : baseEnd_6424899 < baseStart_6424899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424903 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 1, 5]
def baseStart_6424903 : Nat := 118140960795 + 6424903 * 2 ^ 59
def prefixEnd_6424903 : Nat := 4983230072969 + 3 ^ 40 * 6424903 * 2
def baseEnd_6424903 : Nat := 1099687799171327090388305

theorem tailTrace_6424903 : CollatzResearch.WordTrace tailWord_6424903 prefixEnd_6424903 1099687799171327090388305 := by
  unfold tailWord_6424903
  simp only [CollatzResearch.WordTrace]
  refine ⟨234335463842681191918103363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156223642561787461278735575 234335463842681191918103363)
  ·
    refine ⟨351503195764021787877155045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234335463842681191918103363 351503195764021787877155045)
    ·
      refine ⟨65906849205754085226966571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351503195764021787877155045 65906849205754085226966571)
      ·
        refine ⟨98860273808631127840449857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65906849205754085226966571 98860273808631127840449857)
        ·
          refine ⟨74145205356473345880337393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98860273808631127840449857 74145205356473345880337393)
          ·
            refine ⟨55608904017355009410253045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74145205356473345880337393 55608904017355009410253045)
            ·
              refine ⟨5213334751627032132211223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55608904017355009410253045 5213334751627032132211223)
              ·
                refine ⟨7820002127440548198316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213334751627032132211223 7820002127440548198316835)
                ·
                  refine ⟨11730003191160822297475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820002127440548198316835 11730003191160822297475253)
                  ·
                    refine ⟨1099687799171327090388305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11730003191160822297475253 1099687799171327090388305)
                    ·
                      rfl

theorem cell23_6424903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_6424903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424903 prefixEnd_6424903 := by exact prefixLift 6424903
  have htrace : WordTrace (prefixWord ++ tailWord_6424903) baseStart_6424903 baseEnd_6424903 := by
    simpa [prefixWord, tailWord_6424903, baseEnd_6424903] using wordTrace_append hprefix tailTrace_6424903
  have hstable : (prefixWord ++ tailWord_6424903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424903).length < 2 ^ (prefixWord ++ tailWord_6424903).sum := by decide
  have hdescent : baseEnd_6424903 < baseStart_6424903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424917 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6424917 : Nat := 118140960795 + 6424917 * 2 ^ 59
def prefixEnd_6424917 : Nat := 4983230072969 + 3 ^ 40 * 6424917 * 2
def baseEnd_6424917 : Nat := 3299070586243144216389851

theorem tailTrace_6424917 : CollatzResearch.WordTrace tailWord_6424917 prefixEnd_6424917 3299070586243144216389851 := by
  unfold tailWord_6424917
  simp only [CollatzResearch.WordTrace]
  refine ⟨234335974464630472309113005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156223982976420314872742003 234335974464630472309113005)
  ·
    refine ⟨87875990424236427115917377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234335974464630472309113005 87875990424236427115917377)
    ·
      refine ⟨65906992818177320336938033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87875990424236427115917377 65906992818177320336938033)
      ·
        refine ⟨49430244613632990252703525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65906992818177320336938033 49430244613632990252703525)
        ·
          refine ⟨9268170865056185672381911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49430244613632990252703525 9268170865056185672381911)
          ·
            refine ⟨13902256297584278508572867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268170865056185672381911 13902256297584278508572867)
            ·
              refine ⟨20853384446376417762859301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902256297584278508572867 20853384446376417762859301)
              ·
                refine ⟨3910009583695578330536119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20853384446376417762859301 3910009583695578330536119)
                ·
                  refine ⟨5865014375543367495804179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910009583695578330536119 5865014375543367495804179)
                  ·
                    refine ⟨8797521563315051243706269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865014375543367495804179 8797521563315051243706269)
                    ·
                      refine ⟨3299070586243144216389851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797521563315051243706269 3299070586243144216389851)
                      ·
                        rfl

theorem cell23_6424917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6424917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424917 prefixEnd_6424917 := by exact prefixLift 6424917
  have htrace : WordTrace (prefixWord ++ tailWord_6424917) baseStart_6424917 baseEnd_6424917 := by
    simpa [prefixWord, tailWord_6424917, baseEnd_6424917] using wordTrace_append hprefix tailTrace_6424917
  have hstable : (prefixWord ++ tailWord_6424917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424917).length < 2 ^ (prefixWord ++ tailWord_6424917).sum := by decide
  have hdescent : baseEnd_6424917 < baseStart_6424917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424933 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_6424933 : Nat := 118140960795 + 6424933 * 2 ^ 59
def prefixEnd_6424933 : Nat := 4983230072969 + 3 ^ 40 * 6424933 * 2
def baseEnd_6424933 : Nat := 1099692933977872051263259

theorem tailTrace_6424933 : CollatzResearch.WordTrace tailWord_6424933 prefixEnd_6424933 1099692933977872051263259 := by
  unfold tailWord_6424933
  simp only [CollatzResearch.WordTrace]
  refine ⟨234336558032572507041695453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156224372021715004694463635 234336558032572507041695453)
  ·
    refine ⟨87876209262214690140635795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234336558032572507041695453 87876209262214690140635795)
    ·
      refine ⟨131814313893322035210953693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87876209262214690140635795 131814313893322035210953693)
      ·
        refine ⟨49430367709995763204107635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131814313893322035210953693 49430367709995763204107635)
        ·
          refine ⟨74145551564993644806161453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49430367709995763204107635 74145551564993644806161453)
          ·
            refine ⟨27804581836872616802310545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74145551564993644806161453 27804581836872616802310545)
            ·
              refine ⟨20853436377654462601732909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27804581836872616802310545 20853436377654462601732909)
              ·
                refine ⟨7820038641620423475649841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20853436377654462601732909 7820038641620423475649841)
                ·
                  refine ⟨5865028981215317606737381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7820038641620423475649841 5865028981215317606737381)
                  ·
                    refine ⟨1099692933977872051263259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865028981215317606737381 1099692933977872051263259)
                    ·
                      rfl

theorem cell23_6424933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_6424933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424933 prefixEnd_6424933 := by exact prefixLift 6424933
  have htrace : WordTrace (prefixWord ++ tailWord_6424933) baseStart_6424933 baseEnd_6424933 := by
    simpa [prefixWord, tailWord_6424933, baseEnd_6424933] using wordTrace_append hprefix tailTrace_6424933
  have hstable : (prefixWord ++ tailWord_6424933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424933).length < 2 ^ (prefixWord ++ tailWord_6424933).sum := by decide
  have hdescent : baseEnd_6424933 < baseStart_6424933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424956 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_6424956 : Nat := 118140960795 + 6424956 * 2 ^ 59
def prefixEnd_6424956 : Nat := 4983230072969 + 3 ^ 40 * 6424956 * 2
def baseEnd_6424956 : Nat := 3299090611988669563802171

theorem tailTrace_6424956 : CollatzResearch.WordTrace tailWord_6424956 prefixEnd_6424956 3299090611988669563802171 := by
  unfold tailWord_6424956
  simp only [CollatzResearch.WordTrace]
  refine ⟨117168698455744590984891361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156224931274326121313188481 117168698455744590984891361)
  ·
    refine ⟨87876523841808443238668521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117168698455744590984891361 87876523841808443238668521)
    ·
      refine ⟨65907392881356332429001391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87876523841808443238668521 65907392881356332429001391)
      ·
        refine ⟨98861089322034498643502087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65907392881356332429001391 98861089322034498643502087)
        ·
          refine ⟨148291633983051747965253131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98861089322034498643502087 148291633983051747965253131)
          ·
            refine ⟨222437450974577621947879697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148291633983051747965253131 222437450974577621947879697)
            ·
              refine ⟨166828088230933216460909773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222437450974577621947879697 166828088230933216460909773)
              ·
                refine ⟨62560533086599956172841165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166828088230933216460909773 62560533086599956172841165)
                ·
                  refine ⟨23460199907474983564815437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62560533086599956172841165 23460199907474983564815437)
                  ·
                    refine ⟨8797574965303118836805789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23460199907474983564815437 8797574965303118836805789)
                    ·
                      refine ⟨3299090611988669563802171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797574965303118836805789 3299090611988669563802171)
                      ·
                        rfl

theorem cell23_6424956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_6424956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424956 prefixEnd_6424956 := by exact prefixLift 6424956
  have htrace : WordTrace (prefixWord ++ tailWord_6424956) baseStart_6424956 baseEnd_6424956 := by
    simpa [prefixWord, tailWord_6424956, baseEnd_6424956] using wordTrace_append hprefix tailTrace_6424956
  have hstable : (prefixWord ++ tailWord_6424956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424956).length < 2 ^ (prefixWord ++ tailWord_6424956).sum := by decide
  have hdescent : baseEnd_6424956 < baseStart_6424956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424957 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_6424957 : Nat := 118140960795 + 6424957 * 2 ^ 59
def prefixEnd_6424957 : Nat := 4983230072969 + 3 ^ 40 * 6424957 * 2
def baseEnd_6424957 : Nat := 3299091125469324059889667

theorem tailTrace_6424957 : CollatzResearch.WordTrace tailWord_6424957 prefixEnd_6424957 3299091125469324059889667 := by
  unfold tailWord_6424957
  simp only [CollatzResearch.WordTrace]
  refine ⟨234337433384485559140569125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156224955589657039427046083 234337433384485559140569125)
  ·
    refine ⟨43938268759591042338856711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234337433384485559140569125 43938268759591042338856711)
    ·
      refine ⟨65907403139386563508285067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43938268759591042338856711 65907403139386563508285067)
      ·
        refine ⟨98861104709079845262427601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65907403139386563508285067 98861104709079845262427601)
        ·
          refine ⟨74145828531809883946820701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98861104709079845262427601 74145828531809883946820701)
          ·
            refine ⟨27804685699428706480057763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74145828531809883946820701 27804685699428706480057763)
            ·
              refine ⟨41707028549143059720086645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27804685699428706480057763 41707028549143059720086645)
              ·
                refine ⟨3910033926482161848758123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41707028549143059720086645 3910033926482161848758123)
                ·
                  refine ⟨5865050889723242773137185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910033926482161848758123 5865050889723242773137185)
                  ·
                    refine ⟨4398788167292432079852889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865050889723242773137185 4398788167292432079852889)
                    ·
                      refine ⟨3299091125469324059889667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398788167292432079852889 3299091125469324059889667)
                      ·
                        rfl

theorem cell23_6424957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_6424957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424957 prefixEnd_6424957 := by exact prefixLift 6424957
  have htrace : WordTrace (prefixWord ++ tailWord_6424957) baseStart_6424957 baseEnd_6424957 := by
    simpa [prefixWord, tailWord_6424957, baseEnd_6424957] using wordTrace_append hprefix tailTrace_6424957
  have hstable : (prefixWord ++ tailWord_6424957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424957).length < 2 ^ (prefixWord ++ tailWord_6424957).sum := by decide
  have hdescent : baseEnd_6424957 < baseStart_6424957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424959 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 7]
def baseStart_6424959 : Nat := 118140960795 + 6424959 * 2 ^ 59
def prefixEnd_6424959 : Nat := 4983230072969 + 3 ^ 40 * 6424959 * 2
def baseEnd_6424959 : Nat := 1099697384143544350688219

theorem tailTrace_6424959 : CollatzResearch.WordTrace tailWord_6424959 prefixEnd_6424959 1099697384143544350688219 := by
  unfold tailWord_6424959
  simp only [CollatzResearch.WordTrace]
  refine ⟨234337506330478313482141931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156225004220318875654761287 234337506330478313482141931)
  ·
    refine ⟨351506259495717470223212897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234337506330478313482141931 351506259495717470223212897)
    ·
      refine ⟨263629694621788102667409673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351506259495717470223212897 263629694621788102667409673)
      ·
        refine ⟨197722270966341077000557255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263629694621788102667409673 197722270966341077000557255)
        ·
          refine ⟨296583406449511615500835883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197722270966341077000557255 296583406449511615500835883)
          ·
            refine ⟨444875109674267423251253825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296583406449511615500835883 444875109674267423251253825)
            ·
              refine ⟨333656332255700567438440369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444875109674267423251253825 333656332255700567438440369)
              ·
                refine ⟨250242249191775425578830277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333656332255700567438440369 250242249191775425578830277)
                ·
                  refine ⟨46920421723457892296030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250242249191775425578830277 46920421723457892296030677)
                  ·
                    refine ⟨1099697384143544350688219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46920421723457892296030677 1099697384143544350688219)
                    ·
                      rfl

theorem cell23_6424959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_6424959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424959 prefixEnd_6424959 := by exact prefixLift 6424959
  have htrace : WordTrace (prefixWord ++ tailWord_6424959) baseStart_6424959 baseEnd_6424959 := by
    simpa [prefixWord, tailWord_6424959, baseEnd_6424959] using wordTrace_append hprefix tailTrace_6424959
  have hstable : (prefixWord ++ tailWord_6424959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424959).length < 2 ^ (prefixWord ++ tailWord_6424959).sum := by decide
  have hdescent : baseEnd_6424959 < baseStart_6424959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424974 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6424974 : Nat := 118140960795 + 6424974 * 2 ^ 59
def prefixEnd_6424974 : Nat := 4983230072969 + 3 ^ 40 * 6424974 * 2
def baseEnd_6424974 : Nat := 3299099854640450493377089

theorem tailTrace_6424974 : CollatzResearch.WordTrace tailWord_6424974 prefixEnd_6424974 3299099854640450493377089 := by
  unfold tailWord_6424974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29292256678177996380492247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156225368950282647362625317 29292256678177996380492247)
  ·
    refine ⟨43938385017266994570738371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29292256678177996380492247 43938385017266994570738371)
    ·
      refine ⟨65907577525900491856107557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43938385017266994570738371 65907577525900491856107557)
      ·
        refine ⟨12357670786106342223020167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65907577525900491856107557 12357670786106342223020167)
        ·
          refine ⟨18536506179159513334530251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12357670786106342223020167 18536506179159513334530251)
          ·
            refine ⟨27804759268739270001795377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18536506179159513334530251 27804759268739270001795377)
            ·
              refine ⟨20853569451554452501346533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27804759268739270001795377 20853569451554452501346533)
              ·
                refine ⟨3910044272166459844002475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20853569451554452501346533 3910044272166459844002475)
                ·
                  refine ⟨5865066408249689766003713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910044272166459844002475 5865066408249689766003713)
                  ·
                    refine ⟨4398799806187267324502785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865066408249689766003713 4398799806187267324502785)
                    ·
                      refine ⟨3299099854640450493377089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398799806187267324502785 3299099854640450493377089)
                      ·
                        rfl

theorem cell23_6424974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6424974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424974 prefixEnd_6424974 := by exact prefixLift 6424974
  have htrace : WordTrace (prefixWord ++ tailWord_6424974) baseStart_6424974 baseEnd_6424974 := by
    simpa [prefixWord, tailWord_6424974, baseEnd_6424974] using wordTrace_append hprefix tailTrace_6424974
  have hstable : (prefixWord ++ tailWord_6424974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424974).length < 2 ^ (prefixWord ++ tailWord_6424974).sum := by decide
  have hdescent : baseEnd_6424974 < baseStart_6424974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424983 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_6424983 : Nat := 118140960795 + 6424983 * 2 ^ 59
def prefixEnd_6424983 : Nat := 4983230072969 + 3 ^ 40 * 6424983 * 2
def baseEnd_6424983 : Nat := 3299104475966340958164547

theorem tailTrace_6424983 : CollatzResearch.WordTrace tailWord_6424983 prefixEnd_6424983 3299104475966340958164547 := by
  unfold tailWord_6424983
  simp only [CollatzResearch.WordTrace]
  refine ⟨234338381682391365581015603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156225587788260910387343735 234338381682391365581015603)
  ·
    refine ⟨351507572523587048371523405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234338381682391365581015603 351507572523587048371523405)
    ·
      refine ⟨131815339696345143139321277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351507572523587048371523405 131815339696345143139321277)
      ·
        refine ⟨49430752386129428677245479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131815339696345143139321277 49430752386129428677245479)
        ·
          refine ⟨74146128579194143015868219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49430752386129428677245479 74146128579194143015868219)
          ·
            refine ⟨111219192868791214523802329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74146128579194143015868219 111219192868791214523802329)
            ·
              refine ⟨83414394651593410892851747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111219192868791214523802329 83414394651593410892851747)
              ·
                refine ⟨125121591977390116339277621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83414394651593410892851747 125121591977390116339277621)
                ·
                  refine ⟨11730149247880323406807277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125121591977390116339277621 11730149247880323406807277)
                  ·
                    refine ⟨4398805967955121277552729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11730149247880323406807277 4398805967955121277552729)
                    ·
                      refine ⟨3299104475966340958164547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398805967955121277552729 3299104475966340958164547)
                      ·
                        rfl

theorem cell23_6424983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_6424983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424983 prefixEnd_6424983 := by exact prefixLift 6424983
  have htrace : WordTrace (prefixWord ++ tailWord_6424983) baseStart_6424983 baseEnd_6424983 := by
    simpa [prefixWord, tailWord_6424983, baseEnd_6424983] using wordTrace_append hprefix tailTrace_6424983
  have hstable : (prefixWord ++ tailWord_6424983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424983).length < 2 ^ (prefixWord ++ tailWord_6424983).sum := by decide
  have hdescent : baseEnd_6424983 < baseStart_6424983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424996 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_6424996 : Nat := 118140960795 + 6424996 * 2 ^ 59
def prefixEnd_6424996 : Nat := 4983230072969 + 3 ^ 40 * 6424996 * 2
def baseEnd_6424996 : Nat := 3299111151214849407301987

theorem tailTrace_6424996 : CollatzResearch.WordTrace tailWord_6424996 prefixEnd_6424996 3299111151214849407301987 := by
  unfold tailWord_6424996
  simp only [CollatzResearch.WordTrace]
  refine ⟨117169427915672134400619421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156225903887562845867492561 117169427915672134400619421)
  ·
    refine ⟨43938535468377050400232283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117169427915672134400619421 43938535468377050400232283)
    ·
      refine ⟨65907803202565575600348425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43938535468377050400232283 65907803202565575600348425)
      ·
        refine ⟨49430852401924181700261319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65907803202565575600348425 49430852401924181700261319)
        ·
          refine ⟨74146278602886272550391979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49430852401924181700261319 74146278602886272550391979)
          ·
            refine ⟨111219417904329408825587969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74146278602886272550391979 111219417904329408825587969)
            ·
              refine ⟨83414563428247056619190977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111219417904329408825587969 83414563428247056619190977)
              ·
                refine ⟨62560922571185292464393233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83414563428247056619190977 62560922571185292464393233)
                ·
                  refine ⟨46920691928388969348294925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62560922571185292464393233 46920691928388969348294925)
                  ·
                    refine ⟨17595259473145863505610597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46920691928388969348294925 17595259473145863505610597)
                    ·
                      refine ⟨3299111151214849407301987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595259473145863505610597 3299111151214849407301987)
                      ·
                        rfl

theorem cell23_6424996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_6424996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424996 prefixEnd_6424996 := by exact prefixLift 6424996
  have htrace : WordTrace (prefixWord ++ tailWord_6424996) baseStart_6424996 baseEnd_6424996 := by
    simpa [prefixWord, tailWord_6424996, baseEnd_6424996] using wordTrace_append hprefix tailTrace_6424996
  have hstable : (prefixWord ++ tailWord_6424996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424996).length < 2 ^ (prefixWord ++ tailWord_6424996).sum := by decide
  have hdescent : baseEnd_6424996 < baseStart_6424996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425016 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_6425016 : Nat := 118140960795 + 6425016 * 2 ^ 59
def prefixEnd_6425016 : Nat := 4983230072969 + 3 ^ 40 * 6425016 * 2
def baseEnd_6425016 : Nat := 3299121420827939329051895

theorem tailTrace_6425016 : CollatzResearch.WordTrace tailWord_6425016 prefixEnd_6425016 3299121420827939329051895 := by
  unfold tailWord_6425016
  simp only [CollatzResearch.WordTrace]
  refine ⟨117169792645635906108483451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156226390194181208144644601 117169792645635906108483451)
  ·
    refine ⟨175754688968453859162725177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117169792645635906108483451 175754688968453859162725177)
    ·
      refine ⟨131816016726340394372043883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175754688968453859162725177 131816016726340394372043883)
      ·
        refine ⟨197724025089510591558065825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131816016726340394372043883 197724025089510591558065825)
        ·
          refine ⟨148293018817132943668549369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197724025089510591558065825 148293018817132943668549369)
          ·
            refine ⟨111219764112849707751412027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148293018817132943668549369 111219764112849707751412027)
            ·
              refine ⟨166829646169274561627118041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111219764112849707751412027 166829646169274561627118041)
              ·
                refine ⟨125122234626955921220338531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166829646169274561627118041 125122234626955921220338531)
                ·
                  refine ⟨187683351940433881830507797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125122234626955921220338531 187683351940433881830507797)
                  ·
                    refine ⟨8797657122207838210805053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 187683351940433881830507797 8797657122207838210805053)
                    ·
                      refine ⟨3299121420827939329051895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797657122207838210805053 3299121420827939329051895)
                      ·
                        rfl

theorem cell23_6425016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_6425016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425016 prefixEnd_6425016 := by exact prefixLift 6425016
  have htrace : WordTrace (prefixWord ++ tailWord_6425016) baseStart_6425016 baseEnd_6425016 := by
    simpa [prefixWord, tailWord_6425016, baseEnd_6425016] using wordTrace_append hprefix tailTrace_6425016
  have hstable : (prefixWord ++ tailWord_6425016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425016).length < 2 ^ (prefixWord ++ tailWord_6425016).sum := by decide
  have hdescent : baseEnd_6425016 < baseStart_6425016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425025 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6425025 : Nat := 118140960795 + 6425025 * 2 ^ 59
def prefixEnd_6425025 : Nat := 4983230072969 + 3 ^ 40 * 6425025 * 2
def baseEnd_6425025 : Nat := 3299126042153829793839355

theorem tailTrace_6425025 : CollatzResearch.WordTrace tailWord_6425025 prefixEnd_6425025 3299126042153829793839355 := by
  unfold tailWord_6425025
  simp only [CollatzResearch.WordTrace]
  refine ⟨234339913548239206754044529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156226609032159471169363019 234339913548239206754044529)
  ·
    refine ⟨175754935161179405065533397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234339913548239206754044529 175754935161179405065533397)
    ·
      refine ⟨4119256292840142306223439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 175754935161179405065533397 4119256292840142306223439)
      ·
        refine ⟨6178884439260213459335159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119256292840142306223439 6178884439260213459335159)
        ·
          refine ⟨9268326658890320189002739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178884439260213459335159 9268326658890320189002739)
          ·
            refine ⟨13902489988335480283504109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268326658890320189002739 13902489988335480283504109)
            ·
              refine ⟨5213433745625805106314041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13902489988335480283504109 5213433745625805106314041)
              ·
                refine ⟨3910075309219353829735531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213433745625805106314041 3910075309219353829735531)
                ·
                  refine ⟨5865112963829030744603297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910075309219353829735531 5865112963829030744603297)
                  ·
                    refine ⟨4398834722871773058452473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865112963829030744603297 4398834722871773058452473)
                    ·
                      refine ⟨3299126042153829793839355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398834722871773058452473 3299126042153829793839355)
                      ·
                        rfl

theorem cell23_6425025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6425025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425025 prefixEnd_6425025 := by exact prefixLift 6425025
  have htrace : WordTrace (prefixWord ++ tailWord_6425025) baseStart_6425025 baseEnd_6425025 := by
    simpa [prefixWord, tailWord_6425025, baseEnd_6425025] using wordTrace_append hprefix tailTrace_6425025
  have hstable : (prefixWord ++ tailWord_6425025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425025).length < 2 ^ (prefixWord ++ tailWord_6425025).sum := by decide
  have hdescent : baseEnd_6425025 < baseStart_6425025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425094 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6425094 : Nat := 118140960795 + 6425094 * 2 ^ 59
def prefixEnd_6425094 : Nat := 4983230072969 + 3 ^ 40 * 6425094 * 2
def baseEnd_6425094 : Nat := 3299161472318990023876537

theorem tailTrace_6425094 : CollatzResearch.WordTrace tailWord_6425094 prefixEnd_6425094 3299161472318990023876537 := by
  unfold tailWord_6425094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323200943280913485572073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156228286789992821025537557 7323200943280913485572073)
  ·
    refine ⟨5492400707460685114179055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7323200943280913485572073 5492400707460685114179055)
    ·
      refine ⟨8238601061191027671268583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492400707460685114179055 8238601061191027671268583)
      ·
        refine ⟨12357901591786541506902875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8238601061191027671268583 12357901591786541506902875)
        ·
          refine ⟨18536852387679812260354313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12357901591786541506902875 18536852387679812260354313)
          ·
            refine ⟨13902639290759859195265735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18536852387679812260354313 13902639290759859195265735)
            ·
              refine ⟨20853958936139788792898603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902639290759859195265735 20853958936139788792898603)
              ·
                refine ⟨31280938404209683189347905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20853958936139788792898603 31280938404209683189347905)
                ·
                  refine ⟨23460703803157262392010929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31280938404209683189347905 23460703803157262392010929)
                  ·
                    refine ⟨17595527852367946794008197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23460703803157262392010929 17595527852367946794008197)
                    ·
                      refine ⟨3299161472318990023876537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595527852367946794008197 3299161472318990023876537)
                      ·
                        rfl

theorem cell23_6425094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6425094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425094 prefixEnd_6425094 := by exact prefixLift 6425094
  have htrace : WordTrace (prefixWord ++ tailWord_6425094) baseStart_6425094 baseEnd_6425094 := by
    simpa [prefixWord, tailWord_6425094, baseEnd_6425094] using wordTrace_append hprefix tailTrace_6425094
  have hstable : (prefixWord ++ tailWord_6425094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425094).length < 2 ^ (prefixWord ++ tailWord_6425094).sum := by decide
  have hdescent : baseEnd_6425094 < baseStart_6425094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425096 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6425096 : Nat := 118140960795 + 6425096 * 2 ^ 59
def prefixEnd_6425096 : Nat := 4983230072969 + 3 ^ 40 * 6425096 * 2
def baseEnd_6425096 : Nat := 1099720833093433005350509

theorem tailTrace_6425096 : CollatzResearch.WordTrace tailWord_6425096 prefixEnd_6425096 1099720833093433005350509 := by
  unfold tailWord_6425096
  simp only [CollatzResearch.WordTrace]
  refine ⟨117171251565490992939939571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156228335420654657253252761 117171251565490992939939571)
  ·
    refine ⟨175756877348236489409909357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117171251565490992939939571 175756877348236489409909357)
    ·
      refine ⟨65908829005588683528716009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175756877348236489409909357 65908829005588683528716009)
      ·
        refine ⟨49431621754191512646537007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65908829005588683528716009 49431621754191512646537007)
        ·
          refine ⟨74147432631287268969805511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49431621754191512646537007 74147432631287268969805511)
          ·
            refine ⟨111221148946930903454708267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74147432631287268969805511 111221148946930903454708267)
            ·
              refine ⟨166831723420396355182062401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111221148946930903454708267 166831723420396355182062401)
              ·
                refine ⟨125123792565297266386546801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166831723420396355182062401 125123792565297266386546801)
                ·
                  refine ⟨93842844423972949789910101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125123792565297266386546801 93842844423972949789910101)
                  ·
                    refine ⟨1099720833093433005350509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93842844423972949789910101 1099720833093433005350509)
                    ·
                      rfl

theorem cell23_6425096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6425096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425096 prefixEnd_6425096 := by exact prefixLift 6425096
  have htrace : WordTrace (prefixWord ++ tailWord_6425096) baseStart_6425096 baseEnd_6425096 := by
    simpa [prefixWord, tailWord_6425096, baseEnd_6425096] using wordTrace_append hprefix tailTrace_6425096
  have hstable : (prefixWord ++ tailWord_6425096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425096).length < 2 ^ (prefixWord ++ tailWord_6425096).sum := by decide
  have hdescent : baseEnd_6425096 < baseStart_6425096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425103 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 6, 2]
def baseStart_6425103 : Nat := 118140960795 + 6425103 * 2 ^ 59
def prefixEnd_6425103 : Nat := 4983230072969 + 3 ^ 40 * 6425103 * 2
def baseEnd_6425103 : Nat := 3299166093644880488663995

theorem tailTrace_6425103 : CollatzResearch.WordTrace tailWord_6425103 prefixEnd_6425103 3299166093644880488663995 := by
  unfold tailWord_6425103
  simp only [CollatzResearch.WordTrace]
  refine ⟨234342758441956626075383963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156228505627971084050255975 234342758441956626075383963)
  ·
    refine ⟨351514137662934939113075945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234342758441956626075383963 351514137662934939113075945)
    ·
      refine ⟨263635603247201204334806959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351514137662934939113075945 263635603247201204334806959)
      ·
        refine ⟨395453404870801806502210439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263635603247201204334806959 395453404870801806502210439)
        ·
          refine ⟨593180107306202709753315659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395453404870801806502210439 593180107306202709753315659)
          ·
            refine ⟨889770160959304064629973489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593180107306202709753315659 889770160959304064629973489)
            ·
              refine ⟨667327620719478048472480117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889770160959304064629973489 667327620719478048472480117)
              ·
                refine ⟨62561964442451067044295011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667327620719478048472480117 62561964442451067044295011)
                ·
                  refine ⟨93842946663676600566442517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62561964442451067044295011 93842946663676600566442517)
                  ·
                    refine ⟨4398888124859840651551993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93842946663676600566442517 4398888124859840651551993)
                    ·
                      refine ⟨3299166093644880488663995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398888124859840651551993 3299166093644880488663995)
                      ·
                        rfl

theorem cell23_6425103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6, 2].length) (baseStart_6425103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425103 prefixEnd_6425103 := by exact prefixLift 6425103
  have htrace : WordTrace (prefixWord ++ tailWord_6425103) baseStart_6425103 baseEnd_6425103 := by
    simpa [prefixWord, tailWord_6425103, baseEnd_6425103] using wordTrace_append hprefix tailTrace_6425103
  have hstable : (prefixWord ++ tailWord_6425103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425103).length < 2 ^ (prefixWord ++ tailWord_6425103).sum := by decide
  have hdescent : baseEnd_6425103 < baseStart_6425103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425113 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_6425113 : Nat := 118140960795 + 6425113 * 2 ^ 59
def prefixEnd_6425113 : Nat := 4983230072969 + 3 ^ 40 * 6425113 * 2
def baseEnd_6425113 : Nat := 1099723742817141816512983

theorem tailTrace_6425113 : CollatzResearch.WordTrace tailWord_6425113 prefixEnd_6425113 1099723742817141816512983 := by
  unfold tailWord_6425113
  simp only [CollatzResearch.WordTrace]
  refine ⟨234343123171920397783247993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156228748781280265188831995 234343123171920397783247993)
  ·
    refine ⟨175757342378940298337435995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234343123171920397783247993 175757342378940298337435995)
    ·
      refine ⟨263636013568410447506153993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175757342378940298337435995 263636013568410447506153993)
      ·
        refine ⟨197727010176307835629615495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263636013568410447506153993 197727010176307835629615495)
        ·
          refine ⟨296590515264461753444423243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197727010176307835629615495 296590515264461753444423243)
          ·
            refine ⟨444885772896692630166634865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296590515264461753444423243 444885772896692630166634865)
            ·
              refine ⟨333664329672519472624976149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444885772896692630166634865 333664329672519472624976149)
              ·
                refine ⟨15640515453399350279295757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333664329672519472624976149 15640515453399350279295757)
                ·
                  refine ⟨5865193295024756354735909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15640515453399350279295757 5865193295024756354735909)
                  ·
                    refine ⟨1099723742817141816512983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865193295024756354735909 1099723742817141816512983)
                    ·
                      rfl

theorem cell23_6425113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_6425113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425113 prefixEnd_6425113 := by exact prefixLift 6425113
  have htrace : WordTrace (prefixWord ++ tailWord_6425113) baseStart_6425113 baseEnd_6425113 := by
    simpa [prefixWord, tailWord_6425113, baseEnd_6425113] using wordTrace_append hprefix tailTrace_6425113
  have hstable : (prefixWord ++ tailWord_6425113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425113).length < 2 ^ (prefixWord ++ tailWord_6425113).sum := by decide
  have hdescent : baseEnd_6425113 < baseStart_6425113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425120 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6425120 : Nat := 118140960795 + 6425120 * 2 ^ 59
def prefixEnd_6425120 : Nat := 4983230072969 + 3 ^ 40 * 6425120 * 2
def baseEnd_6425120 : Nat := 3299174822816006922151417

theorem tailTrace_6425120 : CollatzResearch.WordTrace tailWord_6425120 prefixEnd_6425120 3299174822816006922151417 := by
  unfold tailWord_6425120
  simp only [CollatzResearch.WordTrace]
  refine ⟨117171689241447518989376407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156228918988596691985835209 117171689241447518989376407)
  ·
    refine ⟨175757533862171278484064611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117171689241447518989376407 175757533862171278484064611)
    ·
      refine ⟨263636300793256917726096917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175757533862171278484064611 263636300793256917726096917)
      ·
        refine ⟨12357951599683918018410793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 263636300793256917726096917 12357951599683918018410793)
        ·
          refine ⟨9268463699762938513808095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12357951599683918018410793 9268463699762938513808095)
          ·
            refine ⟨13902695549644407770712143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268463699762938513808095 13902695549644407770712143)
            ·
              refine ⟨20854043324466611656068215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902695549644407770712143 20854043324466611656068215)
              ·
                refine ⟨31281064986699917484102323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20854043324466611656068215 31281064986699917484102323)
                ·
                  refine ⟨46921597480049876226153485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31281064986699917484102323 46921597480049876226153485)
                  ·
                    refine ⟨17595599055018703584807557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46921597480049876226153485 17595599055018703584807557)
                    ·
                      refine ⟨3299174822816006922151417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595599055018703584807557 3299174822816006922151417)
                      ·
                        rfl

theorem cell23_6425120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6425120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425120 prefixEnd_6425120 := by exact prefixLift 6425120
  have htrace : WordTrace (prefixWord ++ tailWord_6425120) baseStart_6425120 baseEnd_6425120 := by
    simpa [prefixWord, tailWord_6425120, baseEnd_6425120] using wordTrace_append hprefix tailTrace_6425120
  have hstable : (prefixWord ++ tailWord_6425120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425120).length < 2 ^ (prefixWord ++ tailWord_6425120).sum := by decide
  have hdescent : baseEnd_6425120 < baseStart_6425120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425173 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6425173 : Nat := 118140960795 + 6425173 * 2 ^ 59
def prefixEnd_6425173 : Nat := 4983230072969 + 3 ^ 40 * 6425173 * 2
def baseEnd_6425173 : Nat := 1099734012430231738262891

theorem tailTrace_6425173 : CollatzResearch.WordTrace tailWord_6425173 prefixEnd_6425173 1099734012430231738262891 := by
  unfold tailWord_6425173
  simp only [CollatzResearch.WordTrace]
  refine ⟨234345311551703028030432173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156230207701135352020288115 234345311551703028030432173)
  ·
    refine ⟨87879491831888635511412065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234345311551703028030432173 87879491831888635511412065)
    ·
      refine ⟨65909618873916476633559049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87879491831888635511412065 65909618873916476633559049)
      ·
        refine ⟨49432214155437357475169287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65909618873916476633559049 49432214155437357475169287)
        ·
          refine ⟨74148321233156036212753931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49432214155437357475169287 74148321233156036212753931)
          ·
            refine ⟨111222481849734054319130897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74148321233156036212753931 111222481849734054319130897)
            ·
              refine ⟨83416861387300540739348173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111222481849734054319130897 83416861387300540739348173)
              ·
                refine ⟨31281323020237702777255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83416861387300540739348173 31281323020237702777255565)
                ·
                  refine ⟨11730496132589138541470837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31281323020237702777255565 11730496132589138541470837)
                  ·
                    refine ⟨1099734012430231738262891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11730496132589138541470837 1099734012430231738262891)
                    ·
                      rfl

theorem cell23_6425173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6425173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425173 prefixEnd_6425173 := by exact prefixLift 6425173
  have htrace : WordTrace (prefixWord ++ tailWord_6425173) baseStart_6425173 baseEnd_6425173 := by
    simpa [prefixWord, tailWord_6425173, baseEnd_6425173] using wordTrace_append hprefix tailTrace_6425173
  have hstable : (prefixWord ++ tailWord_6425173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425173).length < 2 ^ (prefixWord ++ tailWord_6425173).sum := by decide
  have hdescent : baseEnd_6425173 < baseStart_6425173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425193 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_6425193 : Nat := 118140960795 + 6425193 * 2 ^ 59
def prefixEnd_6425193 : Nat := 4983230072969 + 3 ^ 40 * 6425193 * 2
def baseEnd_6425193 : Nat := 3299212306903785136538581

theorem tailTrace_6425193 : CollatzResearch.WordTrace tailWord_6425193 prefixEnd_6425193 3299212306903785136538581 := by
  unfold tailWord_6425193
  simp only [CollatzResearch.WordTrace]
  refine ⟨234346041011630571446160233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156230694007753714297440155 234346041011630571446160233)
  ·
    refine ⟨175759530758722928584620175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234346041011630571446160233 175759530758722928584620175)
    ·
      refine ⟨263639296138084392876930263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175759530758722928584620175 263639296138084392876930263)
      ·
        refine ⟨395458944207126589315395395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263639296138084392876930263 395458944207126589315395395)
        ·
          refine ⟨593188416310689883973093093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395458944207126589315395395 593188416310689883973093093)
          ·
            refine ⟨111222828058254353244954955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593188416310689883973093093 111222828058254353244954955)
            ·
              refine ⟨166834242087381529867432433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111222828058254353244954955 166834242087381529867432433)
              ·
                refine ⟨125125681565536147400574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166834242087381529867432433 125125681565536147400574325)
                ·
                  refine ⟨11730532646769013818803843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125125681565536147400574325 11730532646769013818803843)
                  ·
                    refine ⟨17595798970153520728205765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11730532646769013818803843 17595798970153520728205765)
                    ·
                      refine ⟨3299212306903785136538581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595798970153520728205765 3299212306903785136538581)
                      ·
                        rfl

theorem cell23_6425193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_6425193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425193 prefixEnd_6425193 := by exact prefixLift 6425193
  have htrace : WordTrace (prefixWord ++ tailWord_6425193) baseStart_6425193 baseEnd_6425193 := by
    simpa [prefixWord, tailWord_6425193, baseEnd_6425193] using wordTrace_append hprefix tailTrace_6425193
  have hstable : (prefixWord ++ tailWord_6425193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425193).length < 2 ^ (prefixWord ++ tailWord_6425193).sum := by decide
  have hdescent : baseEnd_6425193 < baseStart_6425193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425197 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6425197 : Nat := 118140960795 + 6425197 * 2 ^ 59
def prefixEnd_6425197 : Nat := 4983230072969 + 3 ^ 40 * 6425197 * 2
def baseEnd_6425197 : Nat := 3299214360826403120888563

theorem tailTrace_6425197 : CollatzResearch.WordTrace tailWord_6425197 prefixEnd_6425197 3299214360826403120888563 := by
  unfold tailWord_6425197
  simp only [CollatzResearch.WordTrace]
  refine ⟨234346186903616080129305845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156230791269077386752870563 234346186903616080129305845)
  ·
    refine ⟨21969955022214007512122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234346186903616080129305845 21969955022214007512122423)
    ·
      refine ⟨32954932533321011268183635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21969955022214007512122423 32954932533321011268183635)
      ·
        refine ⟨49432398799981516902275453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32954932533321011268183635 49432398799981516902275453)
        ·
          refine ⟨18537149549993068838353295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49432398799981516902275453 18537149549993068838353295)
          ·
            refine ⟨27805724324989603257529943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18537149549993068838353295 27805724324989603257529943)
            ·
              refine ⟨41708586487484404886294915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27805724324989603257529943 41708586487484404886294915)
              ·
                refine ⟨62562879731226607329442373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41708586487484404886294915 62562879731226607329442373)
                ·
                  refine ⟨11730539949604988874270445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62562879731226607329442373 11730539949604988874270445)
                  ·
                    refine ⟨4398952481101870827851417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11730539949604988874270445 4398952481101870827851417)
                    ·
                      refine ⟨3299214360826403120888563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398952481101870827851417 3299214360826403120888563)
                      ·
                        rfl

theorem cell23_6425197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6425197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425197 prefixEnd_6425197 := by exact prefixLift 6425197
  have htrace : WordTrace (prefixWord ++ tailWord_6425197) baseStart_6425197 baseEnd_6425197 := by
    simpa [prefixWord, tailWord_6425197, baseEnd_6425197] using wordTrace_append hprefix tailTrace_6425197
  have hstable : (prefixWord ++ tailWord_6425197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425197).length < 2 ^ (prefixWord ++ tailWord_6425197).sum := by decide
  have hdescent : baseEnd_6425197 < baseStart_6425197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425223 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_6425223 : Nat := 118140960795 + 6425223 * 2 ^ 59
def prefixEnd_6425223 : Nat := 4983230072969 + 3 ^ 40 * 6425223 * 2
def baseEnd_6425223 : Nat := 3299227711323420019163443

theorem tailTrace_6425223 : CollatzResearch.WordTrace tailWord_6425223 prefixEnd_6425223 3299227711323420019163443 := by
  unfold tailWord_6425223
  simp only [CollatzResearch.WordTrace]
  refine ⟨234347135201521886569752323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156231423467681257713168215 234347135201521886569752323)
  ·
    refine ⟨351520702802282829854628485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234347135201521886569752323 351520702802282829854628485)
    ·
      refine ⟨65910131775428030597742841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351520702802282829854628485 65910131775428030597742841)
      ·
        refine ⟨49432598831571022948307131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65910131775428030597742841 49432598831571022948307131)
        ·
          refine ⟨74148898247356534422460697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49432598831571022948307131 74148898247356534422460697)
          ·
            refine ⟨55611673685517400816845523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74148898247356534422460697 55611673685517400816845523)
            ·
              refine ⟨83417510528276101225268285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55611673685517400816845523 83417510528276101225268285)
              ·
                refine ⟨31281566448103537959475607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83417510528276101225268285 31281566448103537959475607)
                ·
                  refine ⟨46922349672155306939213411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31281566448103537959475607 46922349672155306939213411)
                  ·
                    refine ⟨70383524508232960408820117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46922349672155306939213411 70383524508232960408820117)
                    ·
                      refine ⟨3299227711323420019163443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70383524508232960408820117 3299227711323420019163443)
                      ·
                        rfl

theorem cell23_6425223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_6425223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425223 prefixEnd_6425223 := by exact prefixLift 6425223
  have htrace : WordTrace (prefixWord ++ tailWord_6425223) baseStart_6425223 baseEnd_6425223 := by
    simpa [prefixWord, tailWord_6425223, baseEnd_6425223] using wordTrace_append hprefix tailTrace_6425223
  have hstable : (prefixWord ++ tailWord_6425223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425223).length < 2 ^ (prefixWord ++ tailWord_6425223).sum := by decide
  have hdescent : baseEnd_6425223 < baseStart_6425223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425240 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6425240 : Nat := 118140960795 + 6425240 * 2 ^ 59
def prefixEnd_6425240 : Nat := 4983230072969 + 3 ^ 40 * 6425240 * 2
def baseEnd_6425240 : Nat := 3299236440494546452650865

theorem tailTrace_6425240 : CollatzResearch.WordTrace tailWord_6425240 prefixEnd_6425240 3299236440494546452650865 := by
  unfold tailWord_6425240
  simp only [CollatzResearch.WordTrace]
  refine ⟨117173877621230149236560587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156231836828306865648747449 117173877621230149236560587)
  ·
    refine ⟨175760816431845223854840881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117173877621230149236560587 175760816431845223854840881)
    ·
      refine ⟨131820612323883917891130661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175760816431845223854840881 131820612323883917891130661)
      ·
        refine ⟨24716364810728234604586999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131820612323883917891130661 24716364810728234604586999)
        ·
          refine ⟨37074547216092351906880499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24716364810728234604586999 37074547216092351906880499)
          ·
            refine ⟨55611820824138527860320749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37074547216092351906880499 55611820824138527860320749)
            ·
              refine ⟨20854432809051947947620281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55611820824138527860320749 20854432809051947947620281)
              ·
                refine ⟨15640824606788960960715211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20854432809051947947620281 15640824606788960960715211)
                ·
                  refine ⟨23461236910183441441072817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15640824606788960960715211 23461236910183441441072817)
                  ·
                    refine ⟨17595927682637581080804613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23461236910183441441072817 17595927682637581080804613)
                    ·
                      refine ⟨3299236440494546452650865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595927682637581080804613 3299236440494546452650865)
                      ·
                        rfl

theorem cell23_6425240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6425240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425240 prefixEnd_6425240 := by exact prefixLift 6425240
  have htrace : WordTrace (prefixWord ++ tailWord_6425240) baseStart_6425240 baseEnd_6425240 := by
    simpa [prefixWord, tailWord_6425240, baseEnd_6425240] using wordTrace_append hprefix tailTrace_6425240
  have hstable : (prefixWord ++ tailWord_6425240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425240).length < 2 ^ (prefixWord ++ tailWord_6425240).sum := by decide
  have hdescent : baseEnd_6425240 < baseStart_6425240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425244 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6425244 : Nat := 118140960795 + 6425244 * 2 ^ 59
def prefixEnd_6425244 : Nat := 4983230072969 + 3 ^ 40 * 6425244 * 2
def baseEnd_6425244 : Nat := 3299238494417164437000847

theorem tailTrace_6425244 : CollatzResearch.WordTrace tailWord_6425244 prefixEnd_6425244 3299238494417164437000847 := by
  unfold tailWord_6425244
  simp only [CollatzResearch.WordTrace]
  refine ⟨117173950567222903578133393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156231934089630538104177857 117173950567222903578133393)
  ·
    refine ⟨87880462925417177683600045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117173950567222903578133393 87880462925417177683600045)
    ·
      refine ⟨32955173597031441631350017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87880462925417177683600045 32955173597031441631350017)
      ·
        refine ⟨24716380197773581223512513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32955173597031441631350017 24716380197773581223512513)
        ·
          refine ⟨18537285148330185917634385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24716380197773581223512513 18537285148330185917634385)
          ·
            refine ⟨13902963861247639438225789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18537285148330185917634385 13902963861247639438225789)
            ·
              refine ⟨5213611447967864789334671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13902963861247639438225789 5213611447967864789334671)
              ·
                refine ⟨7820417171951797184002007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213611447967864789334671 7820417171951797184002007)
                ·
                  refine ⟨11730625757927695776003011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820417171951797184002007 11730625757927695776003011)
                  ·
                    refine ⟨17595938636891543664004517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11730625757927695776003011 17595938636891543664004517)
                    ·
                      refine ⟨3299238494417164437000847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17595938636891543664004517 3299238494417164437000847)
                      ·
                        rfl

theorem cell23_6425244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6425244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425244 prefixEnd_6425244 := by exact prefixLift 6425244
  have htrace : WordTrace (prefixWord ++ tailWord_6425244) baseStart_6425244 baseEnd_6425244 := by
    simpa [prefixWord, tailWord_6425244, baseEnd_6425244] using wordTrace_append hprefix tailTrace_6425244
  have hstable : (prefixWord ++ tailWord_6425244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425244).length < 2 ^ (prefixWord ++ tailWord_6425244).sum := by decide
  have hdescent : baseEnd_6425244 < baseStart_6425244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425255 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6425255 : Nat := 118140960795 + 6425255 * 2 ^ 59
def prefixEnd_6425255 : Nat := 4983230072969 + 3 ^ 40 * 6425255 * 2
def baseEnd_6425255 : Nat := 3299244142704363893963297

theorem tailTrace_6425255 : CollatzResearch.WordTrace tailWord_6425255 prefixEnd_6425255 3299244142704363893963297 := by
  unfold tailWord_6425255
  simp only [CollatzResearch.WordTrace]
  refine ⟨234348302337405956034917219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156232201558270637356611479 234348302337405956034917219)
  ·
    refine ⟨351522453506108934052375829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234348302337405956034917219 351522453506108934052375829)
    ·
      refine ⟨16477615008098856283705117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 351522453506108934052375829 16477615008098856283705117)
      ·
        refine ⟨6179105628037071106389419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16477615008098856283705117 6179105628037071106389419)
        ·
          refine ⟨9268658442055606659584129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179105628037071106389419 9268658442055606659584129)
          ·
            refine ⟨6951493831541704994688097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9268658442055606659584129 6951493831541704994688097)
            ·
              refine ⟨5213620373656278746016073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951493831541704994688097 5213620373656278746016073)
              ·
                refine ⟨3910215280242209059512055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213620373656278746016073 3910215280242209059512055)
                ·
                  refine ⟨5865322920363313589268083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910215280242209059512055 5865322920363313589268083)
                  ·
                    refine ⟨8797984380544970383902125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865322920363313589268083 8797984380544970383902125)
                    ·
                      refine ⟨3299244142704363893963297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8797984380544970383902125 3299244142704363893963297)
                      ·
                        rfl

theorem cell23_6425255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6425255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425255 prefixEnd_6425255 := by exact prefixLift 6425255
  have htrace : WordTrace (prefixWord ++ tailWord_6425255) baseStart_6425255 baseEnd_6425255 := by
    simpa [prefixWord, tailWord_6425255, baseEnd_6425255] using wordTrace_append hprefix tailTrace_6425255
  have hstable : (prefixWord ++ tailWord_6425255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425255).length < 2 ^ (prefixWord ++ tailWord_6425255).sum := by decide
  have hdescent : baseEnd_6425255 < baseStart_6425255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425263 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 7]
def baseStart_6425263 : Nat := 118140960795 + 6425263 * 2 ^ 59
def prefixEnd_6425263 : Nat := 4983230072969 + 3 ^ 40 * 6425263 * 2
def baseEnd_6425263 : Nat := 1099749416849866620887753

theorem tailTrace_6425263 : CollatzResearch.WordTrace tailWord_6425263 prefixEnd_6425263 1099749416849866620887753 := by
  unfold tailWord_6425263
  simp only [CollatzResearch.WordTrace]
  refine ⟨234348594121376973401208443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156232396080917982267472295 234348594121376973401208443)
  ·
    refine ⟨351522891182065460101812665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234348594121376973401208443 351522891182065460101812665)
    ·
      refine ⟨263642168386549095076359499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351522891182065460101812665 263642168386549095076359499)
      ·
        refine ⟨395463252579823642614539249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263642168386549095076359499 395463252579823642614539249)
        ·
          refine ⟨296597439434867731960904437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395463252579823642614539249 296597439434867731960904437)
          ·
            refine ⟨27806009947018849871334791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296597439434867731960904437 27806009947018849871334791)
            ·
              refine ⟨41709014920528274807002187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27806009947018849871334791 41709014920528274807002187)
              ·
                refine ⟨62563522380792412210503281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41709014920528274807002187 62563522380792412210503281)
                ·
                  refine ⟨46922641785594309157877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62563522380792412210503281 46922641785594309157877461)
                  ·
                    refine ⟨1099749416849866620887753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46922641785594309157877461 1099749416849866620887753)
                    ·
                      rfl

theorem cell23_6425263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_6425263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425263 prefixEnd_6425263 := by exact prefixLift 6425263
  have htrace : WordTrace (prefixWord ++ tailWord_6425263) baseStart_6425263 baseEnd_6425263 := by
    simpa [prefixWord, tailWord_6425263, baseEnd_6425263] using wordTrace_append hprefix tailTrace_6425263
  have hstable : (prefixWord ++ tailWord_6425263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425263).length < 2 ^ (prefixWord ++ tailWord_6425263).sum := by decide
  have hdescent : baseEnd_6425263 < baseStart_6425263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425273 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6425273 : Nat := 118140960795 + 6425273 * 2 ^ 59
def prefixEnd_6425273 : Nat := 4983230072969 + 3 ^ 40 * 6425273 * 2
def baseEnd_6425273 : Nat := 3299253385356144823538213

theorem tailTrace_6425273 : CollatzResearch.WordTrace tailWord_6425273 prefixEnd_6425273 3299253385356144823538213 := by
  unfold tailWord_6425273
  simp only [CollatzResearch.WordTrace]
  refine ⟨234348958851340745109072473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156232639234227163406048315 234348958851340745109072473)
  ·
    refine ⟨175761719138505558831804355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234348958851340745109072473 175761719138505558831804355)
    ·
      refine ⟨263642578707758338247706533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175761719138505558831804355 263642578707758338247706533)
      ·
        refine ⟨49432983507704688421444975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263642578707758338247706533 49432983507704688421444975)
        ·
          refine ⟨74149475261557032632167463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49432983507704688421444975 74149475261557032632167463)
          ·
            refine ⟨111224212892335548948251195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74149475261557032632167463 111224212892335548948251195)
            ·
              refine ⟨166836319338503323422376793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111224212892335548948251195 166836319338503323422376793)
              ·
                refine ⟨125127239503877492566782595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166836319338503323422376793 125127239503877492566782595)
                ·
                  refine ⟨187690859255816238850173893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125127239503877492566782595 187690859255816238850173893)
                  ·
                    refine ⟨35192036110465544784407605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187690859255816238850173893 35192036110465544784407605)
                    ·
                      refine ⟨3299253385356144823538213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35192036110465544784407605 3299253385356144823538213)
                      ·
                        rfl

theorem cell23_6425273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6425273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425273 prefixEnd_6425273 := by exact prefixLift 6425273
  have htrace : WordTrace (prefixWord ++ tailWord_6425273) baseStart_6425273 baseEnd_6425273 := by
    simpa [prefixWord, tailWord_6425273, baseEnd_6425273] using wordTrace_append hprefix tailTrace_6425273
  have hstable : (prefixWord ++ tailWord_6425273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425273).length < 2 ^ (prefixWord ++ tailWord_6425273).sum := by decide
  have hdescent : baseEnd_6425273 < baseStart_6425273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425277 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_6425277 : Nat := 118140960795 + 6425277 * 2 ^ 59
def prefixEnd_6425277 : Nat := 4983230072969 + 3 ^ 40 * 6425277 * 2
def baseEnd_6425277 : Nat := 3299255439278762807888195

theorem tailTrace_6425277 : CollatzResearch.WordTrace tailWord_6425277 prefixEnd_6425277 3299255439278762807888195 := by
  unfold tailWord_6425277
  simp only [CollatzResearch.WordTrace]
  refine ⟨234349104743326253792218085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156232736495550835861478723 234349104743326253792218085)
  ·
    refine ⟨43940457139373672586040891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234349104743326253792218085 43940457139373672586040891)
    ·
      refine ⟨65910685709060508879061337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43940457139373672586040891 65910685709060508879061337)
      ·
        refine ⟨49433014281795381659296003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65910685709060508879061337 49433014281795381659296003)
        ·
          refine ⟨74149521422693072488944005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49433014281795381659296003 74149521422693072488944005)
          ·
            refine ⟨13903035266754951091677001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74149521422693072488944005 13903035266754951091677001)
            ·
              refine ⟨10427276450066213318757751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13903035266754951091677001 10427276450066213318757751)
              ·
                refine ⟨15640914675099319978136627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427276450066213318757751 15640914675099319978136627)
                ·
                  refine ⟨23461372012648979967204941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15640914675099319978136627 23461372012648979967204941)
                  ·
                    refine ⟨8798014504743367487701853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23461372012648979967204941 8798014504743367487701853)
                    ·
                      refine ⟨3299255439278762807888195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8798014504743367487701853 3299255439278762807888195)
                      ·
                        rfl

theorem cell23_6425277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_6425277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425277 prefixEnd_6425277 := by exact prefixLift 6425277
  have htrace : WordTrace (prefixWord ++ tailWord_6425277) baseStart_6425277 baseEnd_6425277 := by
    simpa [prefixWord, tailWord_6425277, baseEnd_6425277] using wordTrace_append hprefix tailTrace_6425277
  have hstable : (prefixWord ++ tailWord_6425277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425277).length < 2 ^ (prefixWord ++ tailWord_6425277).sum := by decide
  have hdescent : baseEnd_6425277 < baseStart_6425277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425298 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6425298 : Nat := 118140960795 + 6425298 * 2 ^ 59
def prefixEnd_6425298 : Nat := 4983230072969 + 3 ^ 40 * 6425298 * 2
def baseEnd_6425298 : Nat := 3299266222372507225725599

theorem tailTrace_6425298 : CollatzResearch.WordTrace tailWord_6425298 prefixEnd_6425298 3299266222372507225725599 := by
  unfold tailWord_6425298
  simp only [CollatzResearch.WordTrace]
  refine ⟨58587467669062543594683137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156233247117500116252488365 58587467669062543594683137)
  ·
    refine ⟨43940600751796907696012353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58587467669062543594683137 43940600751796907696012353)
    ·
      refine ⟨32955450563847680772009265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43940600751796907696012353 32955450563847680772009265)
      ·
        refine ⟨24716587922885760579006949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32955450563847680772009265 24716587922885760579006949)
        ·
          refine ⟨4634360235541080108563803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24716587922885760579006949 4634360235541080108563803)
          ·
            refine ⟨6951540353311620162845705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634360235541080108563803 6951540353311620162845705)
            ·
              refine ⟨5213655264983715122134279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951540353311620162845705 5213655264983715122134279)
              ·
                refine ⟨7820482897475572683201419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213655264983715122134279 7820482897475572683201419)
                ·
                  refine ⟨11730724346213359024802129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820482897475572683201419 11730724346213359024802129)
                  ·
                    refine ⟨8798043259660019268601597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11730724346213359024802129 8798043259660019268601597)
                    ·
                      refine ⟨3299266222372507225725599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8798043259660019268601597 3299266222372507225725599)
                      ·
                        rfl

theorem cell23_6425298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6425298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425298 prefixEnd_6425298 := by exact prefixLift 6425298
  have htrace : WordTrace (prefixWord ++ tailWord_6425298) baseStart_6425298 baseEnd_6425298 := by
    simpa [prefixWord, tailWord_6425298, baseEnd_6425298] using wordTrace_append hprefix tailTrace_6425298
  have hstable : (prefixWord ++ tailWord_6425298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425298).length < 2 ^ (prefixWord ++ tailWord_6425298).sum := by decide
  have hdescent : baseEnd_6425298 < baseStart_6425298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425304 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_6425304 : Nat := 118140960795 + 6425304 * 2 ^ 59
def prefixEnd_6425304 : Nat := 4983230072969 + 3 ^ 40 * 6425304 * 2
def baseEnd_6425304 : Nat := 3299269303256434202250571

theorem tailTrace_6425304 : CollatzResearch.WordTrace tailWord_6425304 prefixEnd_6425304 3299269303256434202250571 := by
  unfold tailWord_6425304
  simp only [CollatzResearch.WordTrace]
  refine ⟨117175044757114218701725483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156233393009485624935633977 117175044757114218701725483)
  ·
    refine ⟨175762567135671328052588225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117175044757114218701725483 175762567135671328052588225)
    ·
      refine ⟨131821925351753496039441169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175762567135671328052588225 131821925351753496039441169)
      ·
        refine ⟨98866444013815122029580877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131821925351753496039441169 98866444013815122029580877)
        ·
          refine ⟨37074916505180670761092829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98866444013815122029580877 37074916505180670761092829)
          ·
            refine ⟨13903093689442751535409811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37074916505180670761092829 13903093689442751535409811)
            ·
              refine ⟨20854640534164127303114717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13903093689442751535409811 20854640534164127303114717)
              ·
                refine ⟨7820490200311547738668019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20854640534164127303114717 7820490200311547738668019)
                ·
                  refine ⟨11730735300467321608002029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820490200311547738668019 11730735300467321608002029)
                  ·
                    refine ⟨4399025737675245603000761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11730735300467321608002029 4399025737675245603000761)
                    ·
                      refine ⟨3299269303256434202250571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399025737675245603000761 3299269303256434202250571)
                      ·
                        rfl

theorem cell23_6425304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_6425304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425304 prefixEnd_6425304 := by exact prefixLift 6425304
  have htrace : WordTrace (prefixWord ++ tailWord_6425304) baseStart_6425304 baseEnd_6425304 := by
    simpa [prefixWord, tailWord_6425304, baseEnd_6425304] using wordTrace_append hprefix tailTrace_6425304
  have hstable : (prefixWord ++ tailWord_6425304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425304).length < 2 ^ (prefixWord ++ tailWord_6425304).sum := by decide
  have hdescent : baseEnd_6425304 < baseStart_6425304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425340 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 7]
def baseStart_6425340 : Nat := 118140960795 + 6425340 * 2 ^ 59
def prefixEnd_6425340 : Nat := 4983230072969 + 3 ^ 40 * 6425340 * 2
def baseEnd_6425340 : Nat := 366587532062221784600045

theorem tailTrace_6425340 : CollatzResearch.WordTrace tailWord_6425340 prefixEnd_6425340 366587532062221784600045 := by
  unfold tailWord_6425340
  simp only [CollatzResearch.WordTrace]
  refine ⟨117175701271049007775880737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156234268361398677034507649 117175701271049007775880737)
  ·
    refine ⟨87881775953286755831910553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117175701271049007775880737 87881775953286755831910553)
    ·
      refine ⟨65911331964965066873932915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87881775953286755831910553 65911331964965066873932915)
      ·
        refine ⟨98866997947447600310899373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65911331964965066873932915 98866997947447600310899373)
        ·
          refine ⟨37075124230292850116587265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98866997947447600310899373 37075124230292850116587265)
          ·
            refine ⟨27806343172719637587440449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37075124230292850116587265 27806343172719637587440449)
            ·
              refine ⟨20854757379539728190580337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27806343172719637587440449 20854757379539728190580337)
              ·
                refine ⟨15641068034654796142935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20854757379539728190580337 15641068034654796142935253)
                ·
                  refine ⟨366587532062221784600045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15641068034654796142935253 366587532062221784600045)
                  ·
                    rfl

theorem cell23_6425340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_6425340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425340 prefixEnd_6425340 := by exact prefixLift 6425340
  have htrace : WordTrace (prefixWord ++ tailWord_6425340) baseStart_6425340 baseEnd_6425340 := by
    simpa [prefixWord, tailWord_6425340, baseEnd_6425340] using wordTrace_append hprefix tailTrace_6425340
  have hstable : (prefixWord ++ tailWord_6425340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425340).length < 2 ^ (prefixWord ++ tailWord_6425340).sum := by decide
  have hdescent : baseEnd_6425340 < baseStart_6425340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425377 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6425377 : Nat := 118140960795 + 6425377 * 2 ^ 59
def prefixEnd_6425377 : Nat := 4983230072969 + 3 ^ 40 * 6425377 * 2
def baseEnd_6425377 : Nat := 3299306787344212416637735

theorem tailTrace_6425377 : CollatzResearch.WordTrace tailWord_6425377 prefixEnd_6425377 3299306787344212416637735 := by
  unfold tailWord_6425377
  simp only [CollatzResearch.WordTrace]
  refine ⟨234352752042963970870858385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156235168028642647247238923 234352752042963970870858385)
  ·
    refine ⟨175764564032222978153143789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234352752042963970870858385 175764564032222978153143789)
    ·
      refine ⟨65911711512083616807428921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175764564032222978153143789 65911711512083616807428921)
      ·
        refine ⟨49433783634062712605571691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65911711512083616807428921 49433783634062712605571691)
        ·
          refine ⟨74150675451094068908357537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49433783634062712605571691 74150675451094068908357537)
          ·
            refine ⟨55613006588320551681268153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74150675451094068908357537 55613006588320551681268153)
            ·
              refine ⟨41709754941240413760951115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55613006588320551681268153 41709754941240413760951115)
              ·
                refine ⟨62564632411860620641426673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41709754941240413760951115 62564632411860620641426673)
                ·
                  refine ⟨46923474308895465481070005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62564632411860620641426673 46923474308895465481070005)
                  ·
                    refine ⟨4399075716458949888850313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46923474308895465481070005 4399075716458949888850313)
                    ·
                      refine ⟨3299306787344212416637735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399075716458949888850313 3299306787344212416637735)
                      ·
                        rfl

theorem cell23_6425377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6425377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425377 prefixEnd_6425377 := by exact prefixLift 6425377
  have htrace : WordTrace (prefixWord ++ tailWord_6425377) baseStart_6425377 baseEnd_6425377 := by
    simpa [prefixWord, tailWord_6425377, baseEnd_6425377] using wordTrace_append hprefix tailTrace_6425377
  have hstable : (prefixWord ++ tailWord_6425377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425377).length < 2 ^ (prefixWord ++ tailWord_6425377).sum := by decide
  have hdescent : baseEnd_6425377 < baseStart_6425377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425407 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_6425407 : Nat := 118140960795 + 6425407 * 2 ^ 59
def prefixEnd_6425407 : Nat := 4983230072969 + 3 ^ 40 * 6425407 * 2
def baseEnd_6425407 : Nat := 3299322191763847299262597

theorem tailTrace_6425407 : CollatzResearch.WordTrace tailWord_6425407 prefixEnd_6425407 3299322191763847299262597 := by
  unfold tailWord_6425407
  simp only [CollatzResearch.WordTrace]
  refine ⟨234353846232855285994450475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156235897488570190662966983 234353846232855285994450475)
  ·
    refine ⟨351530769349282928991675713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234353846232855285994450475 351530769349282928991675713)
    ·
      refine ⟨263648077011962196743756785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351530769349282928991675713 263648077011962196743756785)
      ·
        refine ⟨197736057758971647557817589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263648077011962196743756785 197736057758971647557817589)
        ·
          refine ⟨18537755414903591958545399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197736057758971647557817589 18537755414903591958545399)
          ·
            refine ⟨27806633122355387937818099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18537755414903591958545399 27806633122355387937818099)
            ·
              refine ⟨41709949683533081906727149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27806633122355387937818099 41709949683533081906727149)
              ·
                refine ⟨15641231131324905715022681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41709949683533081906727149 15641231131324905715022681)
                ·
                  refine ⟨11730923348493679286267011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15641231131324905715022681 11730923348493679286267011)
                  ·
                    refine ⟨17596385022740518929400517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11730923348493679286267011 17596385022740518929400517)
                    ·
                      refine ⟨3299322191763847299262597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17596385022740518929400517 3299322191763847299262597)
                      ·
                        rfl

theorem cell23_6425407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_6425407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425407 prefixEnd_6425407 := by exact prefixLift 6425407
  have htrace : WordTrace (prefixWord ++ tailWord_6425407) baseStart_6425407 baseEnd_6425407 := by
    simpa [prefixWord, tailWord_6425407, baseEnd_6425407] using wordTrace_append hprefix tailTrace_6425407
  have hstable : (prefixWord ++ tailWord_6425407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425407).length < 2 ^ (prefixWord ++ tailWord_6425407).sum := by decide
  have hdescent : baseEnd_6425407 < baseStart_6425407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425447 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 6]
def baseStart_6425447 : Nat := 118140960795 + 6425447 * 2 ^ 59
def prefixEnd_6425447 : Nat := 4983230072969 + 3 ^ 40 * 6425447 * 2
def baseEnd_6425447 : Nat := 366593636776669682529157

theorem tailTrace_6425447 : CollatzResearch.WordTrace tailWord_6425447 prefixEnd_6425447 366593636776669682529157 := by
  unfold tailWord_6425447
  simp only [CollatzResearch.WordTrace]
  refine ⟨234355305152710372825906595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156236870101806915217271063 234355305152710372825906595)
  ·
    refine ⟨351532957729065559238859893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234355305152710372825906595 351532957729065559238859893)
    ·
      refine ⟨32956214787099896178643115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351532957729065559238859893 32956214787099896178643115)
      ·
        refine ⟨49434322180649844267964673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32956214787099896178643115 49434322180649844267964673)
        ·
          refine ⟨37075741635487383200973505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49434322180649844267964673 37075741635487383200973505)
          ·
            refine ⟨27806806226615537400730129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37075741635487383200973505 27806806226615537400730129)
            ·
              refine ⟨20855104669961653050547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27806806226615537400730129 20855104669961653050547597)
              ·
                refine ⟨7820664251235619893955349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20855104669961653050547597 7820664251235619893955349)
                ·
                  refine ⟨366593636776669682529157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7820664251235619893955349 366593636776669682529157)
                  ·
                    rfl

theorem cell23_6425447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 6].length) (baseStart_6425447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425447 prefixEnd_6425447 := by exact prefixLift 6425447
  have htrace : WordTrace (prefixWord ++ tailWord_6425447) baseStart_6425447 baseEnd_6425447 := by
    simpa [prefixWord, tailWord_6425447, baseEnd_6425447] using wordTrace_append hprefix tailTrace_6425447
  have hstable : (prefixWord ++ tailWord_6425447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425447).length < 2 ^ (prefixWord ++ tailWord_6425447).sum := by decide
  have hdescent : baseEnd_6425447 < baseStart_6425447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425461 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6425461 : Nat := 118140960795 + 6425461 * 2 ^ 59
def prefixEnd_6425461 : Nat := 4983230072969 + 3 ^ 40 * 6425461 * 2
def baseEnd_6425461 : Nat := 3299349919719190087987349

theorem tailTrace_6425461 : CollatzResearch.WordTrace tailWord_6425461 prefixEnd_6425461 3299349919719190087987349 := by
  unfold tailWord_6425461
  simp only [CollatzResearch.WordTrace]
  refine ⟨234355815774659653216916237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156237210516439768811277491 234355815774659653216916237)
  ·
    refine ⟨87883430915497369956343589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234355815774659653216916237 87883430915497369956343589)
    ·
      refine ⟨16478143296655756866814423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87883430915497369956343589 16478143296655756866814423)
      ·
        refine ⟨24717214944983635300221635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478143296655756866814423 24717214944983635300221635)
        ·
          refine ⟨37075822417475452950332453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24717214944983635300221635 37075822417475452950332453)
          ·
            refine ⟨6951716703276647428187335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37075822417475452950332453 6951716703276647428187335)
            ·
              refine ⟨10427575054914971142281003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951716703276647428187335 10427575054914971142281003)
              ·
                refine ⟨15641362582372456713421505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427575054914971142281003 15641362582372456713421505)
                ·
                  refine ⟨11731021936779342535066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15641362582372456713421505 11731021936779342535066129)
                  ·
                    refine ⟨8798266452584506901299597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11731021936779342535066129 8798266452584506901299597)
                    ·
                      refine ⟨3299349919719190087987349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8798266452584506901299597 3299349919719190087987349)
                      ·
                        rfl

theorem cell23_6425461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6425461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425461 prefixEnd_6425461 := by exact prefixLift 6425461
  have htrace : WordTrace (prefixWord ++ tailWord_6425461) baseStart_6425461 baseEnd_6425461 := by
    simpa [prefixWord, tailWord_6425461, baseEnd_6425461] using wordTrace_append hprefix tailTrace_6425461
  have hstable : (prefixWord ++ tailWord_6425461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425461).length < 2 ^ (prefixWord ++ tailWord_6425461).sum := by decide
  have hdescent : baseEnd_6425461 < baseStart_6425461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425484 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_6425484 : Nat := 118140960795 + 6425484 * 2 ^ 59
def prefixEnd_6425484 : Nat := 4983230072969 + 3 ^ 40 * 6425484 * 2
def baseEnd_6425484 : Nat := 3299361729774243497999743

theorem tailTrace_6425484 : CollatzResearch.WordTrace tailWord_6425484 prefixEnd_6425484 3299361729774243497999743 := by
  unfold tailWord_6425484
  simp only [CollatzResearch.WordTrace]
  refine ⟨117178327326788164072501753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156237769769050885430002337 117178327326788164072501753)
  ·
    refine ⟨87883745495091123054376315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117178327326788164072501753 87883745495091123054376315)
    ·
      refine ⟨131825618242636684581564473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87883745495091123054376315 131825618242636684581564473)
      ·
        refine ⟨98869213681977513436173355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131825618242636684581564473 98869213681977513436173355)
        ·
          refine ⟨148303820522966270154260033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98869213681977513436173355 148303820522966270154260033)
          ·
            refine ⟨111227865392224702615695025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148303820522966270154260033 111227865392224702615695025)
            ·
              refine ⟨83420899044168526961771269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111227865392224702615695025 83420899044168526961771269)
              ·
                refine ⟨15641418570781598805332113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83420899044168526961771269 15641418570781598805332113)
                ·
                  refine ⟨11731063928086199103999085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15641418570781598805332113 11731063928086199103999085)
                  ·
                    refine ⟨4399148973032324663999657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11731063928086199103999085 4399148973032324663999657)
                    ·
                      refine ⟨3299361729774243497999743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399148973032324663999657 3299361729774243497999743)
                      ·
                        rfl

theorem cell23_6425484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_6425484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425484 prefixEnd_6425484 := by exact prefixLift 6425484
  have htrace : WordTrace (prefixWord ++ tailWord_6425484) baseStart_6425484 baseEnd_6425484 := by
    simpa [prefixWord, tailWord_6425484, baseEnd_6425484] using wordTrace_append hprefix tailTrace_6425484
  have hstable : (prefixWord ++ tailWord_6425484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425484).length < 2 ^ (prefixWord ++ tailWord_6425484).sum := by decide
  have hdescent : baseEnd_6425484 < baseStart_6425484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425507 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 6]
def baseStart_6425507 : Nat := 118140960795 + 6425507 * 2 ^ 59
def prefixEnd_6425507 : Nat := 4983230072969 + 3 ^ 40 * 6425507 * 2
def baseEnd_6425507 : Nat := 1099791179943098969337379

theorem tailTrace_6425507 : CollatzResearch.WordTrace tailWord_6425507 prefixEnd_6425507 1099791179943098969337379 := by
  unfold tailWord_6425507
  simp only [CollatzResearch.WordTrace]
  refine ⟨234357493532493003073090775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156238329021662002048727183 234357493532493003073090775)
  ·
    refine ⟨351536240298739504609636163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234357493532493003073090775 351536240298739504609636163)
    ·
      refine ⟨527304360448109256914454245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351536240298739504609636163 527304360448109256914454245)
      ·
        refine ⟨98869567584020485671460171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 527304360448109256914454245 98869567584020485671460171)
        ·
          refine ⟨148304351376030728507190257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98869567584020485671460171 148304351376030728507190257)
          ·
            refine ⟨111228263532023046380392693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148304351376030728507190257 111228263532023046380392693)
            ·
              refine ⟨10427649706127160598161815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111228263532023046380392693 10427649706127160598161815)
              ·
                refine ⟨15641474559190740897242723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427649706127160598161815 15641474559190740897242723)
                ·
                  refine ⟨23462211838786111345864085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15641474559190740897242723 23462211838786111345864085)
                  ·
                    refine ⟨1099791179943098969337379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23462211838786111345864085 1099791179943098969337379)
                    ·
                      rfl

theorem cell23_6425507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].length) (baseStart_6425507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425507 prefixEnd_6425507 := by exact prefixLift 6425507
  have htrace : WordTrace (prefixWord ++ tailWord_6425507) baseStart_6425507 baseEnd_6425507 := by
    simpa [prefixWord, tailWord_6425507, baseEnd_6425507] using wordTrace_append hprefix tailTrace_6425507
  have hstable : (prefixWord ++ tailWord_6425507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425507).length < 2 ^ (prefixWord ++ tailWord_6425507).sum := by decide
  have hdescent : baseEnd_6425507 < baseStart_6425507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425511 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6425511 : Nat := 118140960795 + 6425511 * 2 ^ 59
def prefixEnd_6425511 : Nat := 4983230072969 + 3 ^ 40 * 6425511 * 2
def baseEnd_6425511 : Nat := 1099791864583971630787373

theorem tailTrace_6425511 : CollatzResearch.WordTrace tailWord_6425511 prefixEnd_6425511 1099791864583971630787373 := by
  unfold tailWord_6425511
  simp only [CollatzResearch.WordTrace]
  refine ⟨234357639424478511756236387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156238426282985674504157591 234357639424478511756236387)
  ·
    refine ⟨351536459136717767634354581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234357639424478511756236387 351536459136717767634354581)
    ·
      refine ⟨16478271522033645357860371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 351536459136717767634354581 16478271522033645357860371)
      ·
        refine ⟨24717407283050468036790557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478271522033645357860371 24717407283050468036790557)
        ·
          refine ⟨9269027731143925513796459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24717407283050468036790557 9269027731143925513796459)
          ·
            refine ⟨13903541596715888270694689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269027731143925513796459 13903541596715888270694689)
            ·
              refine ⟨10427656197536916203021017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13903541596715888270694689 10427656197536916203021017)
              ·
                refine ⟨7820742148152687152265763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10427656197536916203021017 7820742148152687152265763)
                ·
                  refine ⟨11731113222229030728398645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820742148152687152265763 11731113222229030728398645)
                  ·
                    refine ⟨1099791864583971630787373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11731113222229030728398645 1099791864583971630787373)
                    ·
                      rfl

theorem cell23_6425511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6425511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425511 prefixEnd_6425511 := by exact prefixLift 6425511
  have htrace : WordTrace (prefixWord ++ tailWord_6425511) baseStart_6425511 baseEnd_6425511 := by
    simpa [prefixWord, tailWord_6425511, baseEnd_6425511] using wordTrace_append hprefix tailTrace_6425511
  have hstable : (prefixWord ++ tailWord_6425511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425511).length < 2 ^ (prefixWord ++ tailWord_6425511).sum := by decide
  have hdescent : baseEnd_6425511 < baseStart_6425511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425527 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_6425527 : Nat := 118140960795 + 6425527 * 2 ^ 59
def prefixEnd_6425527 : Nat := 4983230072969 + 3 ^ 40 * 6425527 * 2
def baseEnd_6425527 : Nat := 3299383809442386829762045

theorem tailTrace_6425527 : CollatzResearch.WordTrace tailWord_6425527 prefixEnd_6425527 3299383809442386829762045 := by
  unfold tailWord_6425527
  simp only [CollatzResearch.WordTrace]
  refine ⟨234358222992420546488818835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156238815328280364325879223 234358222992420546488818835)
  ·
    refine ⟨351537334488630819733228253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234358222992420546488818835 351537334488630819733228253)
    ·
      refine ⟨131826500433236557399960595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351537334488630819733228253 131826500433236557399960595)
      ·
        refine ⟨197739750649854836099940893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131826500433236557399960595 197739750649854836099940893)
        ·
          refine ⟨74152406493695563537477835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197739750649854836099940893 74152406493695563537477835)
          ·
            refine ⟨111228609740543345306216753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74152406493695563537477835 111228609740543345306216753)
            ·
              refine ⟨83421457305407508979662565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111228609740543345306216753 83421457305407508979662565)
              ·
                refine ⟨15641523244763907933686731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83421457305407508979662565 15641523244763907933686731)
                ·
                  refine ⟨23462284867145861900530097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15641523244763907933686731 23462284867145861900530097)
                  ·
                    refine ⟨17596713650359396425397573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23462284867145861900530097 17596713650359396425397573)
                    ·
                      refine ⟨3299383809442386829762045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17596713650359396425397573 3299383809442386829762045)
                      ·
                        rfl

theorem cell23_6425527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_6425527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425527 prefixEnd_6425527 := by exact prefixLift 6425527
  have htrace : WordTrace (prefixWord ++ tailWord_6425527) baseStart_6425527 baseEnd_6425527 := by
    simpa [prefixWord, tailWord_6425527, baseEnd_6425527] using wordTrace_append hprefix tailTrace_6425527
  have hstable : (prefixWord ++ tailWord_6425527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425527).length < 2 ^ (prefixWord ++ tailWord_6425527).sum := by decide
  have hdescent : baseEnd_6425527 < baseStart_6425527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425534 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_6425534 : Nat := 118140960795 + 6425534 * 2 ^ 59
def prefixEnd_6425534 : Nat := 4983230072969 + 3 ^ 40 * 6425534 * 2
def baseEnd_6425534 : Nat := 3299387403806968302374513

theorem tailTrace_6425534 : CollatzResearch.WordTrace tailWord_6425534 prefixEnd_6425534 3299387403806968302374513 := by
  unfold tailWord_6425534
  simp only [CollatzResearch.WordTrace]
  refine ⟨29294809787924398335540457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156238985535596791122882437 29294809787924398335540457)
  ·
    refine ⟨21971107340943298751655343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29294809787924398335540457 21971107340943298751655343)
    ·
      refine ⟨32956661011414948127483015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21971107340943298751655343 32956661011414948127483015)
      ·
        refine ⟨49434991517122422191224523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32956661011414948127483015 49434991517122422191224523)
        ·
          refine ⟨74152487275683633286836785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49434991517122422191224523 74152487275683633286836785)
          ·
            refine ⟨55614365456762724965127589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74152487275683633286836785 55614365456762724965127589)
            ·
              refine ⟨10427693523143010930961423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55614365456762724965127589 10427693523143010930961423)
              ·
                refine ⟨15641540284714516396442135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427693523143010930961423 15641540284714516396442135)
                ·
                  refine ⟨23462310427071774594663203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15641540284714516396442135 23462310427071774594663203)
                  ·
                    refine ⟨35193465640607661891994805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23462310427071774594663203 35193465640607661891994805)
                    ·
                      refine ⟨3299387403806968302374513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35193465640607661891994805 3299387403806968302374513)
                      ·
                        rfl

theorem cell23_6425534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_6425534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425534 prefixEnd_6425534 := by exact prefixLift 6425534
  have htrace : WordTrace (prefixWord ++ tailWord_6425534) baseStart_6425534 baseEnd_6425534 := by
    simpa [prefixWord, tailWord_6425534, baseEnd_6425534] using wordTrace_append hprefix tailTrace_6425534
  have hstable : (prefixWord ++ tailWord_6425534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425534).length < 2 ^ (prefixWord ++ tailWord_6425534).sum := by decide
  have hdescent : baseEnd_6425534 < baseStart_6425534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425554 : List Nat := [3, 2, 2, 3, 1, 2, 2, 8]
def baseStart_6425554 : Nat := 118140960795 + 6425554 * 2 ^ 59
def prefixEnd_6425554 : Nat := 4983230072969 + 3 ^ 40 * 6425554 * 2
def baseEnd_6425554 : Nat := 122199913830372526819423

theorem tailTrace_6425554 : CollatzResearch.WordTrace tailWord_6425554 prefixEnd_6425554 122199913830372526819423 := by
  unfold tailWord_6425554
  simp only [CollatzResearch.WordTrace]
  refine ⟨58589801940830682525012929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156239471842215153400034477 58589801940830682525012929)
  ·
    refine ⟨43942351455623011893759697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58589801940830682525012929 43942351455623011893759697)
    ·
      refine ⟨32956763591717258920319773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43942351455623011893759697 32956763591717258920319773)
      ·
        refine ⟨12358786346893972095119915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32956763591717258920319773 12358786346893972095119915)
        ·
          refine ⟨18538179520340958142679873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12358786346893972095119915 18538179520340958142679873)
          ·
            refine ⟨13903634640255718607009905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538179520340958142679873 13903634640255718607009905)
            ·
              refine ⟨10427725980191788955257429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13903634640255718607009905 10427725980191788955257429)
              ·
                refine ⟨122199913830372526819423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10427725980191788955257429 122199913830372526819423)
                ·
                  rfl

theorem cell23_6425554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_6425554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425554 prefixEnd_6425554 := by exact prefixLift 6425554
  have htrace : WordTrace (prefixWord ++ tailWord_6425554) baseStart_6425554 baseEnd_6425554 := by
    simpa [prefixWord, tailWord_6425554, baseEnd_6425554] using wordTrace_append hprefix tailTrace_6425554
  have hstable : (prefixWord ++ tailWord_6425554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425554).length < 2 ^ (prefixWord ++ tailWord_6425554).sum := by decide
  have hdescent : baseEnd_6425554 < baseStart_6425554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425558 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6425558 : Nat := 118140960795 + 6425558 * 2 ^ 59
def prefixEnd_6425558 : Nat := 4983230072969 + 3 ^ 40 * 6425558 * 2
def baseEnd_6425558 : Nat := 1099799909114225402824801

theorem tailTrace_6425558 : CollatzResearch.WordTrace tailWord_6425558 prefixEnd_6425558 1099799909114225402824801 := by
  unfold tailWord_6425558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647459603456764923949833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156239569103538825855464885 14647459603456764923949833)
  ·
    refine ⟨10985594702592573692962375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14647459603456764923949833 10985594702592573692962375)
    ·
      refine ⟨16478392053888860539443563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10985594702592573692962375 16478392053888860539443563)
      ·
        refine ⟨24717588080833290809165345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478392053888860539443563 24717588080833290809165345)
        ·
          refine ⟨18538191060624968106874009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24717588080833290809165345 18538191060624968106874009)
          ·
            refine ⟨13903643295468726080155507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538191060624968106874009 13903643295468726080155507)
            ·
              refine ⟨20855464943203089120233261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13903643295468726080155507 20855464943203089120233261)
              ·
                refine ⟨7820799353701158420087473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20855464943203089120233261 7820799353701158420087473)
                ·
                  refine ⟨5865599515275868815065605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7820799353701158420087473 5865599515275868815065605)
                  ·
                    refine ⟨1099799909114225402824801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865599515275868815065605 1099799909114225402824801)
                    ·
                      rfl

theorem cell23_6425558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6425558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425558 prefixEnd_6425558 := by exact prefixLift 6425558
  have htrace : WordTrace (prefixWord ++ tailWord_6425558) baseStart_6425558 baseEnd_6425558 := by
    simpa [prefixWord, tailWord_6425558, baseEnd_6425558] using wordTrace_append hprefix tailTrace_6425558
  have hstable : (prefixWord ++ tailWord_6425558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425558).length < 2 ^ (prefixWord ++ tailWord_6425558).sum := by decide
  have hdescent : baseEnd_6425558 < baseStart_6425558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425588 : List Nat := [2, 6, 2, 1, 1, 11]
def baseStart_6425588 : Nat := 118140960795 + 6425588 * 2 ^ 59
def prefixEnd_6425588 : Nat := 4983230072969 + 3 ^ 40 * 6425588 * 2
def baseEnd_6425588 : Nat := 13577840048404572391355

theorem tailTrace_6425588 : CollatzResearch.WordTrace tailWord_6425588 prefixEnd_6425588 13577840048404572391355 := by
  unfold tailWord_6425588
  simp only [CollatzResearch.WordTrace]
  refine ⟨117180223922599776953394709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156240298563466369271192945 117180223922599776953394709)
  ·
    refine ⟨5492822996371864544690377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117180223922599776953394709 5492822996371864544690377)
    ·
      refine ⟨4119617247278898408517783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492822996371864544690377 4119617247278898408517783)
      ·
        refine ⟨6179425870918347612776675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119617247278898408517783 6179425870918347612776675)
        ·
          refine ⟨9269138806377521419165013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179425870918347612776675 9269138806377521419165013)
          ·
            refine ⟨13577840048404572391355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9269138806377521419165013 13577840048404572391355)
            ·
              rfl

theorem cell23_6425588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 11].length) (baseStart_6425588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425588 prefixEnd_6425588 := by exact prefixLift 6425588
  have htrace : WordTrace (prefixWord ++ tailWord_6425588) baseStart_6425588 baseEnd_6425588 := by
    simpa [prefixWord, tailWord_6425588, baseEnd_6425588] using wordTrace_append hprefix tailTrace_6425588
  have hstable : (prefixWord ++ tailWord_6425588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425588).length < 2 ^ (prefixWord ++ tailWord_6425588).sum := by decide
  have hdescent : baseEnd_6425588 < baseStart_6425588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425597 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_6425597 : Nat := 118140960795 + 6425597 * 2 ^ 59
def prefixEnd_6425597 : Nat := 4983230072969 + 3 ^ 40 * 6425597 * 2
def baseEnd_6425597 : Nat := 1099806584362733851962241

theorem tailTrace_6425597 : CollatzResearch.WordTrace tailWord_6425597 prefixEnd_6425597 1099806584362733851962241 := by
  unfold tailWord_6425597
  simp only [CollatzResearch.WordTrace]
  refine ⟨234360776102166948443867045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156240517401444632295911363 234360776102166948443867045)
  ·
    refine ⟨43942645519156302833225071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234360776102166948443867045 43942645519156302833225071)
    ·
      refine ⟨65913968278734454249837607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43942645519156302833225071 65913968278734454249837607)
      ·
        refine ⟨98870952418101681374756411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65913968278734454249837607 98870952418101681374756411)
        ·
          refine ⟨148306428627152522062134617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98870952418101681374756411 148306428627152522062134617)
          ·
            refine ⟨111229821470364391546600963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148306428627152522062134617 111229821470364391546600963)
            ·
              refine ⟨166844732205546587319901445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111229821470364391546600963 166844732205546587319901445)
              ·
                refine ⟨31283387288539985122481521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166844732205546587319901445 31283387288539985122481521)
                ·
                  refine ⟨23462540466404988841861141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31283387288539985122481521 23462540466404988841861141)
                  ·
                    refine ⟨1099806584362733851962241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23462540466404988841861141 1099806584362733851962241)
                    ·
                      rfl

theorem cell23_6425597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_6425597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425597 prefixEnd_6425597 := by exact prefixLift 6425597
  have htrace : WordTrace (prefixWord ++ tailWord_6425597) baseStart_6425597 baseEnd_6425597 := by
    simpa [prefixWord, tailWord_6425597, baseEnd_6425597] using wordTrace_append hprefix tailTrace_6425597
  have hstable : (prefixWord ++ tailWord_6425597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425597).length < 2 ^ (prefixWord ++ tailWord_6425597).sum := by decide
  have hdescent : baseEnd_6425597 < baseStart_6425597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425614 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6425614 : Nat := 118140960795 + 6425614 * 2 ^ 59
def prefixEnd_6425614 : Nat := 4983230072969 + 3 ^ 40 * 6425614 * 2
def baseEnd_6425614 : Nat := 1099809494086442663124715

theorem tailTrace_6425614 : CollatzResearch.WordTrace tailWord_6425614 prefixEnd_6425614 1099809494086442663124715 := by
  unfold tailWord_6425614
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295174517888170043404487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156240930762070240231490597 29295174517888170043404487)
  ·
    refine ⟨43942761776832255065106731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29295174517888170043404487 43942761776832255065106731)
    ·
      refine ⟨65914142665248382597660097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43942761776832255065106731 65914142665248382597660097)
      ·
        refine ⟨49435606998936286948245073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65914142665248382597660097 49435606998936286948245073)
        ·
          refine ⟨37076705249202215211183805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49435606998936286948245073 37076705249202215211183805)
          ·
            refine ⟨13903764468450830704193927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37076705249202215211183805 13903764468450830704193927)
            ·
              refine ⟨20855646702676246056290891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13903764468450830704193927 20855646702676246056290891)
              ·
                refine ⟨31283470054014369084436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20855646702676246056290891 31283470054014369084436337)
                ·
                  refine ⟨23462602540510776813327253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31283470054014369084436337 23462602540510776813327253)
                  ·
                    refine ⟨1099809494086442663124715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23462602540510776813327253 1099809494086442663124715)
                    ·
                      rfl

theorem cell23_6425614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6425614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425614 prefixEnd_6425614 := by exact prefixLift 6425614
  have htrace : WordTrace (prefixWord ++ tailWord_6425614) baseStart_6425614 baseEnd_6425614 := by
    simpa [prefixWord, tailWord_6425614, baseEnd_6425614] using wordTrace_append hprefix tailTrace_6425614
  have hstable : (prefixWord ++ tailWord_6425614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425614).length < 2 ^ (prefixWord ++ tailWord_6425614).sum := by decide
  have hdescent : baseEnd_6425614 < baseStart_6425614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425621 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_6425621 : Nat := 118140960795 + 6425621 * 2 ^ 59
def prefixEnd_6425621 : Nat := 4983230072969 + 3 ^ 40 * 6425621 * 2
def baseEnd_6425621 : Nat := 3299432076623909461986613

theorem tailTrace_6425621 : CollatzResearch.WordTrace tailWord_6425621 prefixEnd_6425621 3299432076623909461986613 := by
  unfold tailWord_6425621
  simp only [CollatzResearch.WordTrace]
  refine ⟨234361651454080000542740717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156241100969386667028493811 234361651454080000542740717)
  ·
    refine ⟨87885619295280000203527769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234361651454080000542740717 87885619295280000203527769)
    ·
      refine ⟨65914214471460000152645827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87885619295280000203527769 65914214471460000152645827)
      ·
        refine ⟨98871321707190000228968741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65914214471460000152645827 98871321707190000228968741)
        ·
          refine ⟨18538372820098125042931639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98871321707190000228968741 18538372820098125042931639)
          ·
            refine ⟨27807559230147187564397459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18538372820098125042931639 27807559230147187564397459)
            ·
              refine ⟨41711338845220781346596189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27807559230147187564397459 41711338845220781346596189)
              ·
                refine ⟨15641752066957793004973571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41711338845220781346596189 15641752066957793004973571)
                ·
                  refine ⟨23462628100436689507460357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15641752066957793004973571 23462628100436689507460357)
                  ·
                    refine ⟨4399242768831879282648817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23462628100436689507460357 4399242768831879282648817)
                    ·
                      refine ⟨3299432076623909461986613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399242768831879282648817 3299432076623909461986613)
                      ·
                        rfl

theorem cell23_6425621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_6425621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425621 prefixEnd_6425621 := by exact prefixLift 6425621
  have htrace : WordTrace (prefixWord ++ tailWord_6425621) baseStart_6425621 baseEnd_6425621 := by
    simpa [prefixWord, tailWord_6425621, baseEnd_6425621] using wordTrace_append hprefix tailTrace_6425621
  have hstable : (prefixWord ++ tailWord_6425621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425621).length < 2 ^ (prefixWord ++ tailWord_6425621).sum := by decide
  have hdescent : baseEnd_6425621 < baseStart_6425621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425642 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6425642 : Nat := 118140960795 + 6425642 * 2 ^ 59
def prefixEnd_6425642 : Nat := 4983230072969 + 3 ^ 40 * 6425642 * 2
def baseEnd_6425642 : Nat := 3299442859717653879824017

theorem tailTrace_6425642 : CollatzResearch.WordTrace tailWord_6425642 prefixEnd_6425642 3299442859717653879824017 := by
  unfold tailWord_6425642
  simp only [CollatzResearch.WordTrace]
  refine ⟨58590604346750980282313795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156241611591335947419503453 58590604346750980282313795)
  ·
    refine ⟨87885906520126470423470693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58590604346750980282313795 87885906520126470423470693)
    ·
      refine ⟨16478607472523713204400755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87885906520126470423470693 16478607472523713204400755)
      ·
        refine ⟨24717911208785569806601133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478607472523713204400755 24717911208785569806601133)
        ·
          refine ⟨9269216703294588677475425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24717911208785569806601133 9269216703294588677475425)
          ·
            refine ⟨6951912527470941508106569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269216703294588677475425 6951912527470941508106569)
            ·
              refine ⟨5213934395603206131079927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951912527470941508106569 5213934395603206131079927)
              ·
                refine ⟨7820901593404809196619891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213934395603206131079927 7820901593404809196619891)
                ·
                  refine ⟨11731352390107213794929837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7820901593404809196619891 11731352390107213794929837)
                  ·
                    refine ⟨4399257146290205173098689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11731352390107213794929837 4399257146290205173098689)
                    ·
                      refine ⟨3299442859717653879824017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399257146290205173098689 3299442859717653879824017)
                      ·
                        rfl

theorem cell23_6425642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6425642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425642 prefixEnd_6425642 := by exact prefixLift 6425642
  have htrace : WordTrace (prefixWord ++ tailWord_6425642) baseStart_6425642 baseEnd_6425642 := by
    simpa [prefixWord, tailWord_6425642, baseEnd_6425642] using wordTrace_append hprefix tailTrace_6425642
  have hstable : (prefixWord ++ tailWord_6425642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425642).length < 2 ^ (prefixWord ++ tailWord_6425642).sum := by decide
  have hdescent : baseEnd_6425642 < baseStart_6425642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425661 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 5]
def baseStart_6425661 : Nat := 118140960795 + 6425661 * 2 ^ 59
def prefixEnd_6425661 : Nat := 4983230072969 + 3 ^ 40 * 6425661 * 2
def baseEnd_6425661 : Nat := 366605846205565478387381

theorem tailTrace_6425661 : CollatzResearch.WordTrace tailWord_6425661 prefixEnd_6425661 366605846205565478387381 := by
  unfold tailWord_6425661
  simp only [CollatzResearch.WordTrace]
  refine ⟨234363110373935087374196837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156242073582623391582797891 234363110373935087374196837)
  ·
    refine ⟨43943083195112828882661907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234363110373935087374196837 43943083195112828882661907)
    ·
      refine ⟨65914624792669243323992861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43943083195112828882661907 65914624792669243323992861)
      ·
        refine ⟨24717984297250966246497323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65914624792669243323992861 24717984297250966246497323)
        ·
          refine ⟨37076976445876449369745985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24717984297250966246497323 37076976445876449369745985)
          ·
            refine ⟨27807732334407337027309489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37076976445876449369745985 27807732334407337027309489)
            ·
              refine ⟨20855799250805502770482117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27807732334407337027309489 20855799250805502770482117)
              ·
                refine ⟨3910462359526031769465397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20855799250805502770482117 3910462359526031769465397)
                ·
                  refine ⟨366605846205565478387381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910462359526031769465397 366605846205565478387381)
                  ·
                    rfl

theorem cell23_6425661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_6425661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425661 prefixEnd_6425661 := by exact prefixLift 6425661
  have htrace : WordTrace (prefixWord ++ tailWord_6425661) baseStart_6425661 baseEnd_6425661 := by
    simpa [prefixWord, tailWord_6425661, baseEnd_6425661] using wordTrace_append hprefix tailTrace_6425661
  have hstable : (prefixWord ++ tailWord_6425661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425661).length < 2 ^ (prefixWord ++ tailWord_6425661).sum := by decide
  have hdescent : baseEnd_6425661 < baseStart_6425661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425667 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_6425667 : Nat := 118140960795 + 6425667 * 2 ^ 59
def prefixEnd_6425667 : Nat := 4983230072969 + 3 ^ 40 * 6425667 * 2
def baseEnd_6425667 : Nat := 3299455696734016282011401

theorem tailTrace_6425667 : CollatzResearch.WordTrace tailWord_6425667 prefixEnd_6425667 3299455696734016282011401 := by
  unfold tailWord_6425667
  simp only [CollatzResearch.WordTrace]
  refine ⟨234363329211913350398915255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156242219474608900265943503 234363329211913350398915255)
  ·
    refine ⟨351544993817870025598372883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234363329211913350398915255 351544993817870025598372883)
    ·
      refine ⟨527317490726805038397559325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351544993817870025598372883 527317490726805038397559325)
      ·
        refine ⟨197744059022551889399084747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527317490726805038397559325 197744059022551889399084747)
        ·
          refine ⟨296616088533827834098627121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197744059022551889399084747 296616088533827834098627121)
          ·
            refine ⟨222462066400370875573970341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296616088533827834098627121 222462066400370875573970341)
            ·
              refine ⟨41711637450069539170119439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222462066400370875573970341 41711637450069539170119439)
              ·
                refine ⟨62567456175104308755179159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41711637450069539170119439 62567456175104308755179159)
                ·
                  refine ⟨93851184262656463132768739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62567456175104308755179159 93851184262656463132768739)
                  ·
                    refine ⟨140776776393984694699153109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93851184262656463132768739 140776776393984694699153109)
                    ·
                      refine ⟨3299455696734016282011401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140776776393984694699153109 3299455696734016282011401)
                      ·
                        rfl

theorem cell23_6425667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_6425667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425667 prefixEnd_6425667 := by exact prefixLift 6425667
  have htrace : WordTrace (prefixWord ++ tailWord_6425667) baseStart_6425667 baseEnd_6425667 := by
    simpa [prefixWord, tailWord_6425667, baseEnd_6425667] using wordTrace_append hprefix tailTrace_6425667
  have hstable : (prefixWord ++ tailWord_6425667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425667).length < 2 ^ (prefixWord ++ tailWord_6425667).sum := by decide
  have hdescent : baseEnd_6425667 < baseStart_6425667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425687 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 10]
def baseStart_6425687 : Nat := 118140960795 + 6425687 * 2 ^ 59
def prefixEnd_6425687 : Nat := 4983230072969 + 3 ^ 40 * 6425687 * 2
def baseEnd_6425687 : Nat := 1099821988782368734587103

theorem tailTrace_6425687 : CollatzResearch.WordTrace tailWord_6425687 prefixEnd_6425687 1099821988782368734587103 := by
  unfold tailWord_6425687
  simp only [CollatzResearch.WordTrace]
  refine ⟨234364058671840893814643315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156242705781227262543095543 234364058671840893814643315)
  ·
    refine ⟨351546088007761340721964973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234364058671840893814643315 351546088007761340721964973)
    ·
      refine ⟨131829783002910502770736865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351546088007761340721964973 131829783002910502770736865)
      ·
        refine ⟨98872337252182877078052649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131829783002910502770736865 98872337252182877078052649)
        ·
          refine ⟨74154252939137157808539487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98872337252182877078052649 74154252939137157808539487)
          ·
            refine ⟨111231379408705736712809231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74154252939137157808539487 111231379408705736712809231)
            ·
              refine ⟨166847069113058605069213847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111231379408705736712809231 166847069113058605069213847)
              ·
                refine ⟨250270603669587907603820771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166847069113058605069213847 250270603669587907603820771)
                ·
                  refine ⟨375405905504381861405731157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250270603669587907603820771 375405905504381861405731157)
                  ·
                    refine ⟨1099821988782368734587103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 375405905504381861405731157 1099821988782368734587103)
                    ·
                      rfl

theorem cell23_6425687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_6425687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425687 prefixEnd_6425687 := by exact prefixLift 6425687
  have htrace : WordTrace (prefixWord ++ tailWord_6425687) baseStart_6425687 baseEnd_6425687 := by
    simpa [prefixWord, tailWord_6425687, baseEnd_6425687] using wordTrace_append hprefix tailTrace_6425687
  have hstable : (prefixWord ++ tailWord_6425687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425687).length < 2 ^ (prefixWord ++ tailWord_6425687).sum := by decide
  have hdescent : baseEnd_6425687 < baseStart_6425687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425818 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_6425818 : Nat := 118140960795 + 6425818 * 2 ^ 59
def prefixEnd_6425818 : Nat := 4983230072969 + 3 ^ 40 * 6425818 * 2
def baseEnd_6425818 : Nat := 3299533232312845191223207

theorem tailTrace_6425818 : CollatzResearch.WordTrace tailWord_6425818 prefixEnd_6425818 3299533232312845191223207 := by
  unfold tailWord_6425818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58592209158591575796915527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156245891089577535458441405 58592209158591575796915527)
  ·
    refine ⟨87888313737887363695373291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58592209158591575796915527 87888313737887363695373291)
    ·
      refine ⟨131832470606831045543059937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87888313737887363695373291 131832470606831045543059937)
      ·
        refine ⟨98874352955123284157294953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131832470606831045543059937 98874352955123284157294953)
        ·
          refine ⟨74155764716342463117971215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98874352955123284157294953 74155764716342463117971215)
          ·
            refine ⟨111233647074513694676956823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74155764716342463117971215 111233647074513694676956823)
            ·
              refine ⟨166850470611770542015435235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111233647074513694676956823 166850470611770542015435235)
              ·
                refine ⟨250275705917655813023152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166850470611770542015435235 250275705917655813023152853)
                ·
                  refine ⟨5865836857445058117730145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250275705917655813023152853 5865836857445058117730145)
                  ·
                    refine ⟨4399377643083793588297609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865836857445058117730145 4399377643083793588297609)
                    ·
                      refine ⟨3299533232312845191223207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399377643083793588297609 3299533232312845191223207)
                      ·
                        rfl

theorem cell23_6425818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_6425818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425818 prefixEnd_6425818 := by exact prefixLift 6425818
  have htrace : WordTrace (prefixWord ++ tailWord_6425818) baseStart_6425818 baseEnd_6425818 := by
    simpa [prefixWord, tailWord_6425818, baseEnd_6425818] using wordTrace_append hprefix tailTrace_6425818
  have hstable : (prefixWord ++ tailWord_6425818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425818).length < 2 ^ (prefixWord ++ tailWord_6425818).sum := by decide
  have hdescent : baseEnd_6425818 < baseStart_6425818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425824 : List Nat := [2, 1, 1, 3, 1, 5, 10]
def baseStart_6425824 : Nat := 118140960795 + 6425824 * 2 ^ 59
def prefixEnd_6425824 : Nat := 4983230072969 + 3 ^ 40 * 6425824 * 2
def baseEnd_6425824 : Nat := 40735016212305829231459

theorem tailTrace_6425824 : CollatzResearch.WordTrace tailWord_6425824 prefixEnd_6425824 40735016212305829231459 := by
  unfold tailWord_6425824
  simp only [CollatzResearch.WordTrace]
  refine ⟨117184527736172283106190263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156246036981563044141587017 117184527736172283106190263)
  ·
    refine ⟨175776791604258424659285395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117184527736172283106190263 175776791604258424659285395)
    ·
      refine ⟨263665187406387636988928093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175776791604258424659285395 263665187406387636988928093)
      ·
        refine ⟨98874445277395363870848035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263665187406387636988928093 98874445277395363870848035)
        ·
          refine ⟨148311667916093045806272053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98874445277395363870848035 148311667916093045806272053)
          ·
            refine ⟨13904218867133723044338005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148311667916093045806272053 13904218867133723044338005)
            ·
              refine ⟨40735016212305829231459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13904218867133723044338005 40735016212305829231459)
              ·
                rfl

theorem cell23_6425824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 10].length) (baseStart_6425824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425824 prefixEnd_6425824 := by exact prefixLift 6425824
  have htrace : WordTrace (prefixWord ++ tailWord_6425824) baseStart_6425824 baseEnd_6425824 := by
    simpa [prefixWord, tailWord_6425824, baseEnd_6425824] using wordTrace_append hprefix tailTrace_6425824
  have hstable : (prefixWord ++ tailWord_6425824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425824).length < 2 ^ (prefixWord ++ tailWord_6425824).sum := by decide
  have hdescent : baseEnd_6425824 < baseStart_6425824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425828 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_6425828 : Nat := 118140960795 + 6425828 * 2 ^ 59
def prefixEnd_6425828 : Nat := 4983230072969 + 3 ^ 40 * 6425828 * 2
def baseEnd_6425828 : Nat := 1099846122373130050699387

theorem tailTrace_6425828 : CollatzResearch.WordTrace tailWord_6425828 prefixEnd_6425828 1099846122373130050699387 := by
  unfold tailWord_6425828
  simp only [CollatzResearch.WordTrace]
  refine ⟨117184600682165037447763069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156246134242886716597017425 117184600682165037447763069)
  ·
    refine ⟨43944225255811889042911151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117184600682165037447763069 43944225255811889042911151)
    ·
      refine ⟨65916337883717833564366727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43944225255811889042911151 65916337883717833564366727)
      ·
        refine ⟨98874506825576750346550091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65916337883717833564366727 98874506825576750346550091)
        ·
          refine ⟨148311760238365125519825137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98874506825576750346550091 148311760238365125519825137)
          ·
            refine ⟨111233820178773844139868853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148311760238365125519825137 111233820178773844139868853)
            ·
              refine ⟨10428170641760047888112705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111233820178773844139868853 10428170641760047888112705)
              ·
                refine ⟨7821127981320035916084529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10428170641760047888112705 7821127981320035916084529)
                ·
                  refine ⟨5865845985990026937063397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821127981320035916084529 5865845985990026937063397)
                  ·
                    refine ⟨1099846122373130050699387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865845985990026937063397 1099846122373130050699387)
                    ·
                      rfl

theorem cell23_6425828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_6425828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425828 prefixEnd_6425828 := by exact prefixLift 6425828
  have htrace : WordTrace (prefixWord ++ tailWord_6425828) baseStart_6425828 baseEnd_6425828 := by
    simpa [prefixWord, tailWord_6425828, baseEnd_6425828] using wordTrace_append hprefix tailTrace_6425828
  have hstable : (prefixWord ++ tailWord_6425828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425828).length < 2 ^ (prefixWord ++ tailWord_6425828).sum := by decide
  have hdescent : baseEnd_6425828 < baseStart_6425828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425835 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 3, 2, 2]
def baseStart_6425835 : Nat := 118140960795 + 6425835 * 2 ^ 59
def prefixEnd_6425835 : Nat := 4983230072969 + 3 ^ 40 * 6425835 * 2
def baseEnd_6425835 : Nat := 3299541961483971624710629

theorem tailTrace_6425835 : CollatzResearch.WordTrace tailWord_6425835 prefixEnd_6425835 3299541961483971624710629 := by
  unfold tailWord_6425835
  simp only [CollatzResearch.WordTrace]
  refine ⟨234369456675304715091030959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156246304450203143394020639 234369456675304715091030959)
  ·
    refine ⟨351554185012957072636546439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234369456675304715091030959 351554185012957072636546439)
    ·
      refine ⟨527331277519435608954819659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351554185012957072636546439 527331277519435608954819659)
      ·
        refine ⟨790996916279153413432229489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527331277519435608954819659 790996916279153413432229489)
        ·
          refine ⟨593247687209365060074172117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790996916279153413432229489 593247687209365060074172117)
          ·
            refine ⟨13904242668969493595488409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 593247687209365060074172117 13904242668969493595488409)
            ·
              refine ⟨10428182001727120196616307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13904242668969493595488409 10428182001727120196616307)
              ·
                refine ⟨15642273002590680294924461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428182001727120196616307 15642273002590680294924461)
                ·
                  refine ⟨5865852375971505110596673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15642273002590680294924461 5865852375971505110596673)
                  ·
                    refine ⟨4399389281978628832947505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865852375971505110596673 4399389281978628832947505)
                    ·
                      refine ⟨3299541961483971624710629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399389281978628832947505 3299541961483971624710629)
                      ·
                        rfl

theorem cell23_6425835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2, 2].length) (baseStart_6425835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425835 prefixEnd_6425835 := by exact prefixLift 6425835
  have htrace : WordTrace (prefixWord ++ tailWord_6425835) baseStart_6425835 baseEnd_6425835 := by
    simpa [prefixWord, tailWord_6425835, baseEnd_6425835] using wordTrace_append hprefix tailTrace_6425835
  have hstable : (prefixWord ++ tailWord_6425835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425835).length < 2 ^ (prefixWord ++ tailWord_6425835).sum := by decide
  have hdescent : baseEnd_6425835 < baseStart_6425835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425858 : List Nat := [3, 4, 1, 1, 3, 1, 1, 9]
def baseStart_6425858 : Nat := 118140960795 + 6425858 * 2 ^ 59
def prefixEnd_6425858 : Nat := 4983230072969 + 3 ^ 40 * 6425858 * 2
def baseEnd_6425858 : Nat := 122205695242186112397149

theorem tailTrace_6425858 : CollatzResearch.WordTrace tailWord_6425858 prefixEnd_6425858 122205695242186112397149 := by
  unfold tailWord_6425858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58592573888555347504779557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156246863702814260012745485 58592573888555347504779557)
  ·
    refine ⟨10986107604104127657146167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58592573888555347504779557 10986107604104127657146167)
    ·
      refine ⟨16479161406156191485719251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10986107604104127657146167 16479161406156191485719251)
      ·
        refine ⟨24718742109234287228578877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479161406156191485719251 24718742109234287228578877)
        ·
          refine ⟨9269528290962857710717079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24718742109234287228578877 9269528290962857710717079)
          ·
            refine ⟨13904292436444286566075619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269528290962857710717079 13904292436444286566075619)
            ·
              refine ⟨20856438654666429849113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904292436444286566075619 20856438654666429849113429)
              ·
                refine ⟨122205695242186112397149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20856438654666429849113429 122205695242186112397149)
                ·
                  rfl

theorem cell23_6425858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_6425858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425858 prefixEnd_6425858 := by exact prefixLift 6425858
  have htrace : WordTrace (prefixWord ++ tailWord_6425858) baseStart_6425858 baseEnd_6425858 := by
    simpa [prefixWord, tailWord_6425858, baseEnd_6425858] using wordTrace_append hprefix tailTrace_6425858
  have hstable : (prefixWord ++ tailWord_6425858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425858).length < 2 ^ (prefixWord ++ tailWord_6425858).sum := by decide
  have hdescent : baseEnd_6425858 < baseStart_6425858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425868 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_6425868 : Nat := 118140960795 + 6425868 * 2 ^ 59
def prefixEnd_6425868 : Nat := 4983230072969 + 3 ^ 40 * 6425868 * 2
def baseEnd_6425868 : Nat := 3299558906345569995597977

theorem tailTrace_6425868 : CollatzResearch.WordTrace tailWord_6425868 prefixEnd_6425868 3299558906345569995597977 := by
  unfold tailWord_6425868
  simp only [CollatzResearch.WordTrace]
  refine ⟨117185330142092580863491129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156247106856123441151321505 117185330142092580863491129)
  ·
    refine ⟨87888997606569435647618347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117185330142092580863491129 87888997606569435647618347)
    ·
      refine ⟨131833496409854153471427521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87888997606569435647618347 131833496409854153471427521)
      ·
        refine ⟨98875122307390615103570641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131833496409854153471427521 98875122307390615103570641)
        ·
          refine ⟨74156341730542961327677981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98875122307390615103570641 74156341730542961327677981)
          ·
            refine ⟨27808628148953610497879243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74156341730542961327677981 27808628148953610497879243)
            ·
              refine ⟨41712942223430415746818865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27808628148953610497879243 41712942223430415746818865)
              ·
                refine ⟨31284706667572811810114149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41712942223430415746818865 31284706667572811810114149)
                ·
                  refine ⟨5865882500169902214396403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31284706667572811810114149 5865882500169902214396403)
                  ·
                    refine ⟨8798823750254853321594605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865882500169902214396403 8798823750254853321594605)
                    ·
                      refine ⟨3299558906345569995597977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8798823750254853321594605 3299558906345569995597977)
                      ·
                        rfl

theorem cell23_6425868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_6425868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425868 prefixEnd_6425868 := by exact prefixLift 6425868
  have htrace : WordTrace (prefixWord ++ tailWord_6425868) baseStart_6425868 baseEnd_6425868 := by
    simpa [prefixWord, tailWord_6425868, baseEnd_6425868] using wordTrace_append hprefix tailTrace_6425868
  have hstable : (prefixWord ++ tailWord_6425868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425868).length < 2 ^ (prefixWord ++ tailWord_6425868).sum := by decide
  have hdescent : baseEnd_6425868 < baseStart_6425868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425885 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6425885 : Nat := 118140960795 + 6425885 * 2 ^ 59
def prefixEnd_6425885 : Nat := 4983230072969 + 3 ^ 40 * 6425885 * 2
def baseEnd_6425885 : Nat := 3299567635516696429085399

theorem tailTrace_6425885 : CollatzResearch.WordTrace tailWord_6425885 prefixEnd_6425885 3299567635516696429085399 := by
  unfold tailWord_6425885
  simp only [CollatzResearch.WordTrace]
  refine ⟨234371280325123573630351109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156247520216749049086900739 234371280325123573630351109)
  ·
    refine ⟨43944615060960670055690833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234371280325123573630351109 43944615060960670055690833)
    ·
      refine ⟨32958461295720502541768125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43944615060960670055690833 32958461295720502541768125)
      ·
        refine ⟨12359422985895188453163047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32958461295720502541768125 12359422985895188453163047)
        ·
          refine ⟨18539134478842782679744571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359422985895188453163047 18539134478842782679744571)
          ·
            refine ⟨27808701718264174019616857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18539134478842782679744571 27808701718264174019616857)
            ·
              refine ⟨20856526288698130514712643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27808701718264174019616857 20856526288698130514712643)
              ·
                refine ⟨31284789433047195772068965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20856526288698130514712643 31284789433047195772068965)
                ·
                  refine ⟨5865898018696349207262931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31284789433047195772068965 5865898018696349207262931)
                  ·
                    refine ⟨8798847028044523810894397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865898018696349207262931 8798847028044523810894397)
                    ·
                      refine ⟨3299567635516696429085399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8798847028044523810894397 3299567635516696429085399)
                      ·
                        rfl

theorem cell23_6425885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6425885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425885 prefixEnd_6425885 := by exact prefixLift 6425885
  have htrace : WordTrace (prefixWord ++ tailWord_6425885) baseStart_6425885 baseEnd_6425885 := by
    simpa [prefixWord, tailWord_6425885, baseEnd_6425885] using wordTrace_append hprefix tailTrace_6425885
  have hstable : (prefixWord ++ tailWord_6425885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425885).length < 2 ^ (prefixWord ++ tailWord_6425885).sum := by decide
  have hdescent : baseEnd_6425885 < baseStart_6425885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425886 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6425886 : Nat := 118140960795 + 6425886 * 2 ^ 59
def prefixEnd_6425886 : Nat := 4983230072969 + 3 ^ 40 * 6425886 * 2
def baseEnd_6425886 : Nat := 3299568148997350925172895

theorem tailTrace_6425886 : CollatzResearch.WordTrace tailWord_6425886 prefixEnd_6425886 3299568148997350925172895 := by
  unfold tailWord_6425886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296414599764993850142189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156247544532079967200758341 29296414599764993850142189)
  ·
    refine ⟨10986155474911872693803321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29296414599764993850142189 10986155474911872693803321)
    ·
      refine ⟨8239616606183904520352491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10986155474911872693803321 8239616606183904520352491)
      ·
        refine ⟨12359424909275856780528737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239616606183904520352491 12359424909275856780528737)
        ·
          refine ⟨9269568681956892585396553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359424909275856780528737 9269568681956892585396553)
          ·
            refine ⟨6952176511467669439047415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269568681956892585396553 6952176511467669439047415)
            ·
              refine ⟨10428264767201504158571123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952176511467669439047415 10428264767201504158571123)
              ·
                refine ⟨15642397150802256237856685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428264767201504158571123 15642397150802256237856685)
                ·
                  refine ⟨5865898931550846089196257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15642397150802256237856685 5865898931550846089196257)
                  ·
                    refine ⟨4399424198663134566897193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5865898931550846089196257 4399424198663134566897193)
                    ·
                      refine ⟨3299568148997350925172895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399424198663134566897193 3299568148997350925172895)
                      ·
                        rfl

theorem cell23_6425886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6425886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425886 prefixEnd_6425886 := by exact prefixLift 6425886
  have htrace : WordTrace (prefixWord ++ tailWord_6425886) baseStart_6425886 baseEnd_6425886 := by
    simpa [prefixWord, tailWord_6425886, baseEnd_6425886] using wordTrace_append hprefix tailTrace_6425886
  have hstable : (prefixWord ++ tailWord_6425886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425886).length < 2 ^ (prefixWord ++ tailWord_6425886).sum := by decide
  have hdescent : baseEnd_6425886 < baseStart_6425886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6425968 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2]
def baseStart_6425968 : Nat := 118140960795 + 6425968 * 2 ^ 59
def prefixEnd_6425968 : Nat := 4983230072969 + 3 ^ 40 * 6425968 * 2
def baseEnd_6425968 : Nat := 3299610254411019604347517

theorem tailTrace_6425968 : CollatzResearch.WordTrace tailWord_6425968 prefixEnd_6425968 3299610254411019604347517 := by
  unfold tailWord_6425968
  simp only [CollatzResearch.WordTrace]
  refine ⟨117187153791911439402811279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156249538389215252537081705 117187153791911439402811279)
  ·
    refine ⟨175780730687867159104216919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117187153791911439402811279 175780730687867159104216919)
    ·
      refine ⟨263671096031800738656325379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175780730687867159104216919 263671096031800738656325379)
      ·
        refine ⟨395506644047701107984488069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263671096031800738656325379 395506644047701107984488069)
        ·
          refine ⟨74157495758943957747091513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395506644047701107984488069 74157495758943957747091513)
          ·
            refine ⟨55618121819207968310318635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74157495758943957747091513 55618121819207968310318635)
            ·
              refine ⟨83427182728811952465477953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55618121819207968310318635 83427182728811952465477953)
              ·
                refine ⟨62570387046608964349108465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83427182728811952465477953 62570387046608964349108465)
                ·
                  refine ⟨46927790284956723261831349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62570387046608964349108465 46927790284956723261831349)
                  ·
                    refine ⟨4399480339214692805796689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46927790284956723261831349 4399480339214692805796689)
                    ·
                      refine ⟨3299610254411019604347517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399480339214692805796689 3299610254411019604347517)
                      ·
                        rfl

theorem cell23_6425968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2].length) (baseStart_6425968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6425968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6425968 prefixEnd_6425968 := by exact prefixLift 6425968
  have htrace : WordTrace (prefixWord ++ tailWord_6425968) baseStart_6425968 baseEnd_6425968 := by
    simpa [prefixWord, tailWord_6425968, baseEnd_6425968] using wordTrace_append hprefix tailTrace_6425968
  have hstable : (prefixWord ++ tailWord_6425968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6425968).length < 2 ^ (prefixWord ++ tailWord_6425968).sum := by decide
  have hdescent : baseEnd_6425968 < baseStart_6425968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6425968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426015 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6426015 : Nat := 118140960795 + 6426015 * 2 ^ 59
def prefixEnd_6426015 : Nat := 4983230072969 + 3 ^ 40 * 6426015 * 2
def baseEnd_6426015 : Nat := 3299634388001780920459801

theorem tailTrace_6426015 : CollatzResearch.WordTrace tailWord_6426015 prefixEnd_6426015 3299634388001780920459801 := by
  unfold tailWord_6426015
  simp only [CollatzResearch.WordTrace]
  refine ⟨234376021814652605832583499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156250681209768403888388999 234376021814652605832583499)
  ·
    refine ⟨351564032721978908748875249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234376021814652605832583499 351564032721978908748875249)
    ·
      refine ⟨263673024541484181561656437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351564032721978908748875249 263673024541484181561656437)
      ·
        refine ⟨24719346050764142021405291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263673024541484181561656437 24719346050764142021405291)
        ·
          refine ⟨37079019076146213032107937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24719346050764142021405291 37079019076146213032107937)
          ·
            refine ⟨27809264307109659774080953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37079019076146213032107937 27809264307109659774080953)
            ·
              refine ⟨20856948230332244830560715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27809264307109659774080953 20856948230332244830560715)
              ·
                refine ⟨31285422345498367245841073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20856948230332244830560715 31285422345498367245841073)
                ·
                  refine ⟨23464066759123775434380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31285422345498367245841073 23464066759123775434380805)
                  ·
                    refine ⟨4399512517335707893946401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23464066759123775434380805 4399512517335707893946401)
                    ·
                      refine ⟨3299634388001780920459801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399512517335707893946401 3299634388001780920459801)
                      ·
                        rfl

theorem cell23_6426015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6426015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426015 prefixEnd_6426015 := by exact prefixLift 6426015
  have htrace : WordTrace (prefixWord ++ tailWord_6426015) baseStart_6426015 baseEnd_6426015 := by
    simpa [prefixWord, tailWord_6426015, baseEnd_6426015] using wordTrace_append hprefix tailTrace_6426015
  have hstable : (prefixWord ++ tailWord_6426015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426015).length < 2 ^ (prefixWord ++ tailWord_6426015).sum := by decide
  have hdescent : baseEnd_6426015 < baseStart_6426015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426052 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6426052 : Nat := 118140960795 + 6426052 * 2 ^ 59
def prefixEnd_6426052 : Nat := 4983230072969 + 3 ^ 40 * 6426052 * 2
def baseEnd_6426052 : Nat := 3299653386785997275697131

theorem tailTrace_6426052 : CollatzResearch.WordTrace tailWord_6426052 prefixEnd_6426052 3299653386785997275697131 := by
  unfold tailWord_6426052
  simp only [CollatzResearch.WordTrace]
  refine ⟨117188685657759280575840205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156251580877012374101120273 117188685657759280575840205)
  ·
    refine ⟨43945757121659730215940077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117188685657759280575840205 43945757121659730215940077)
    ·
      refine ⟨16479658920622398830977529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43945757121659730215940077 16479658920622398830977529)
      ·
        refine ⟨12359744190466799123233147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16479658920622398830977529 12359744190466799123233147)
        ·
          refine ⟨18539616285700198684849721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359744190466799123233147 18539616285700198684849721)
          ·
            refine ⟨13904712214275149013637291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18539616285700198684849721 13904712214275149013637291)
            ·
              refine ⟨20857068321412723520455937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904712214275149013637291 20857068321412723520455937)
              ·
                refine ⟨15642801241059542640341953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20857068321412723520455937 15642801241059542640341953)
                ·
                  refine ⟨11732100930794656980256465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15642801241059542640341953 11732100930794656980256465)
                  ·
                    refine ⟨8799075698095992735192349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11732100930794656980256465 8799075698095992735192349)
                    ·
                      refine ⟨3299653386785997275697131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799075698095992735192349 3299653386785997275697131)
                      ·
                        rfl

theorem cell23_6426052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6426052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426052 prefixEnd_6426052 := by exact prefixLift 6426052
  have htrace : WordTrace (prefixWord ++ tailWord_6426052) baseStart_6426052 baseEnd_6426052 := by
    simpa [prefixWord, tailWord_6426052, baseEnd_6426052] using wordTrace_append hprefix tailTrace_6426052
  have hstable : (prefixWord ++ tailWord_6426052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426052).length < 2 ^ (prefixWord ++ tailWord_6426052).sum := by decide
  have hdescent : baseEnd_6426052 < baseStart_6426052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426085 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_6426085 : Nat := 118140960795 + 6426085 * 2 ^ 59
def prefixEnd_6426085 : Nat := 4983230072969 + 3 ^ 40 * 6426085 * 2
def baseEnd_6426085 : Nat := 1099890110549198548861493

theorem tailTrace_6426085 : CollatzResearch.WordTrace tailWord_6426085 prefixEnd_6426085 1099890110549198548861493 := by
  unfold tailWord_6426085
  simp only [CollatzResearch.WordTrace]
  refine ⟨234378574924399007787631709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156252383282932671858421139 234378574924399007787631709)
  ·
    refine ⟨87891965596649627920361891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234378574924399007787631709 87891965596649627920361891)
    ·
      refine ⟨131837948394974441880542837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87891965596649627920361891 131837948394974441880542837)
      ·
        refine ⟨12359807662028853926300891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131837948394974441880542837 12359807662028853926300891)
        ·
          refine ⟨18539711493043280889451337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359807662028853926300891 18539711493043280889451337)
          ·
            refine ⟨13904783619782460667088503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18539711493043280889451337 13904783619782460667088503)
            ·
              refine ⟨20857175429673691000632755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904783619782460667088503 20857175429673691000632755)
              ·
                refine ⟨31285763144510536500949133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20857175429673691000632755 31285763144510536500949133)
                ·
                  refine ⟨11732161179191451187855925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31285763144510536500949133 11732161179191451187855925)
                  ·
                    refine ⟨1099890110549198548861493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11732161179191451187855925 1099890110549198548861493)
                    ·
                      rfl

theorem cell23_6426085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_6426085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426085 prefixEnd_6426085 := by exact prefixLift 6426085
  have htrace : WordTrace (prefixWord ++ tailWord_6426085) baseStart_6426085 baseEnd_6426085 := by
    simpa [prefixWord, tailWord_6426085, baseEnd_6426085] using wordTrace_append hprefix tailTrace_6426085
  have hstable : (prefixWord ++ tailWord_6426085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426085).length < 2 ^ (prefixWord ++ tailWord_6426085).sum := by decide
  have hdescent : baseEnd_6426085 < baseStart_6426085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426110 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6426110 : Nat := 118140960795 + 6426110 * 2 ^ 59
def prefixEnd_6426110 : Nat := 4983230072969 + 3 ^ 40 * 6426110 * 2
def baseEnd_6426110 : Nat := 1099894389554652682923955

theorem tailTrace_6426110 : CollatzResearch.WordTrace tailWord_6426110 prefixEnd_6426110 1099894389554652682923955 := by
  unfold tailWord_6426110
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297435843663554632161473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156252991166205624704861189 29297435843663554632161473)
  ·
    refine ⟨21973076882747665974121105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29297435843663554632161473 21973076882747665974121105)
    ·
      refine ⟨16479807662060749480590829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21973076882747665974121105 16479807662060749480590829)
      ·
        refine ⟨6179927873272781055221561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16479807662060749480590829 6179927873272781055221561)
        ·
          refine ⟨4634945904954585791416171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179927873272781055221561 4634945904954585791416171)
          ·
            refine ⟨6952418857431878687124257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634945904954585791416171 6952418857431878687124257)
            ·
              refine ⟨5214314143073909015343193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952418857431878687124257 5214314143073909015343193)
              ·
                refine ⟨3910735607305431761507395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5214314143073909015343193 3910735607305431761507395)
                ·
                  refine ⟨5866103410958147642261093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910735607305431761507395 5866103410958147642261093)
                  ·
                    refine ⟨1099894389554652682923955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5866103410958147642261093 1099894389554652682923955)
                    ·
                      rfl

theorem cell23_6426110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6426110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426110 prefixEnd_6426110 := by exact prefixLift 6426110
  have htrace : WordTrace (prefixWord ++ tailWord_6426110) baseStart_6426110 baseEnd_6426110 := by
    simpa [prefixWord, tailWord_6426110, baseEnd_6426110] using wordTrace_append hprefix tailTrace_6426110
  have hstable : (prefixWord ++ tailWord_6426110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426110).length < 2 ^ (prefixWord ++ tailWord_6426110).sum := by decide
  have hdescent : baseEnd_6426110 < baseStart_6426110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426116 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6426116 : Nat := 118140960795 + 6426116 * 2 ^ 59
def prefixEnd_6426116 : Nat := 4983230072969 + 3 ^ 40 * 6426116 * 2
def baseEnd_6426116 : Nat := 3299686249547885025296837

theorem tailTrace_6426116 : CollatzResearch.WordTrace tailWord_6426116 prefixEnd_6426116 3299686249547885025296837 := by
  unfold tailWord_6426116
  simp only [CollatzResearch.WordTrace]
  refine ⟨117189852793643350041005101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156253137058191133388006801 117189852793643350041005101)
  ·
    refine ⟨43946194797616256265376913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117189852793643350041005101 43946194797616256265376913)
    ·
      refine ⟨32959646098212192199032685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43946194797616256265376913 32959646098212192199032685)
      ·
        refine ⟨12359867286829572074637257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32959646098212192199032685 12359867286829572074637257)
        ·
          refine ⟨9269900465122179055977943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359867286829572074637257 9269900465122179055977943)
          ·
            refine ⟨13904850697683268583966915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269900465122179055977943 13904850697683268583966915)
            ·
              refine ⟨20857276046524902875950373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904850697683268583966915 20857276046524902875950373)
              ·
                refine ⟨3910739258723419289240695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20857276046524902875950373 3910739258723419289240695)
                ·
                  refine ⟨5866108888085128933861043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910739258723419289240695 5866108888085128933861043)
                  ·
                    refine ⟨8799163332127693400791565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5866108888085128933861043 8799163332127693400791565)
                    ·
                      refine ⟨3299686249547885025296837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799163332127693400791565 3299686249547885025296837)
                      ·
                        rfl

theorem cell23_6426116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6426116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426116 prefixEnd_6426116 := by exact prefixLift 6426116
  have htrace : WordTrace (prefixWord ++ tailWord_6426116) baseStart_6426116 baseEnd_6426116 := by
    simpa [prefixWord, tailWord_6426116, baseEnd_6426116] using wordTrace_append hprefix tailTrace_6426116
  have hstable : (prefixWord ++ tailWord_6426116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426116).length < 2 ^ (prefixWord ++ tailWord_6426116).sum := by decide
  have hdescent : baseEnd_6426116 < baseStart_6426116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426145 : List Nat := [1, 2, 3, 2, 2, 3, 3, 7]
def baseStart_6426145 : Nat := 118140960795 + 6426145 * 2 ^ 59
def prefixEnd_6426145 : Nat := 4983230072969 + 3 ^ 40 * 6426145 * 2
def baseEnd_6426145 : Nat := 122211153351365385623489

theorem tailTrace_6426145 : CollatzResearch.WordTrace tailWord_6426145 prefixEnd_6426145 122211153351365385623489 := by
  unfold tailWord_6426145
  simp only [CollatzResearch.WordTrace]
  refine ⟨234380763304181638034815889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156253842202787758689877259 234380763304181638034815889)
  ·
    refine ⟨175785572478136228526111917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234380763304181638034815889 175785572478136228526111917)
    ·
      refine ⟨65919589679301085697291969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175785572478136228526111917 65919589679301085697291969)
      ·
        refine ⟨49439692259475814272968977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65919589679301085697291969 49439692259475814272968977)
        ·
          refine ⟨37079769194606860704726733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49439692259475814272968977 37079769194606860704726733)
          ·
            refine ⟨13904913447977572764272525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37079769194606860704726733 13904913447977572764272525)
            ·
              refine ⟨5214342542991589786602197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13904913447977572764272525 5214342542991589786602197)
              ·
                refine ⟨122211153351365385623489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5214342542991589786602197 122211153351365385623489)
                ·
                  rfl

theorem cell23_6426145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 7].length) (baseStart_6426145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426145 prefixEnd_6426145 := by exact prefixLift 6426145
  have htrace : WordTrace (prefixWord ++ tailWord_6426145) baseStart_6426145 baseEnd_6426145 := by
    simpa [prefixWord, tailWord_6426145, baseEnd_6426145] using wordTrace_append hprefix tailTrace_6426145
  have hstable : (prefixWord ++ tailWord_6426145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426145).length < 2 ^ (prefixWord ++ tailWord_6426145).sum := by decide
  have hdescent : baseEnd_6426145 < baseStart_6426145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426166 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6426166 : Nat := 118140960795 + 6426166 * 2 ^ 59
def prefixEnd_6426166 : Nat := 4983230072969 + 3 ^ 40 * 6426166 * 2
def baseEnd_6426166 : Nat := 1099903974526869943223869

theorem tailTrace_6426166 : CollatzResearch.WordTrace tailWord_6426166 prefixEnd_6426166 1099903974526869943223869 := by
  unfold tailWord_6426166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648845577319097413833147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156254352824737039080886901 14648845577319097413833147)
  ·
    refine ⟨21973268365978646120749721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14648845577319097413833147 21973268365978646120749721)
    ·
      refine ⟨16479951274483984590562291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21973268365978646120749721 16479951274483984590562291)
      ·
        refine ⟨24719926911725976885843437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479951274483984590562291 24719926911725976885843437)
        ·
          refine ⟨9269972591897241332191289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24719926911725976885843437 9269972591897241332191289)
          ·
            refine ⟨6952479443922930999143467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269972591897241332191289 6952479443922930999143467)
            ·
              refine ⟨10428719165884396498715201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952479443922930999143467 10428719165884396498715201)
              ·
                refine ⟨7821539374413297374036401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10428719165884396498715201 7821539374413297374036401)
                ·
                  refine ⟨5866154530809973030527301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821539374413297374036401 5866154530809973030527301)
                  ·
                    refine ⟨1099903974526869943223869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5866154530809973030527301 1099903974526869943223869)
                    ·
                      rfl

theorem cell23_6426166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6426166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426166 prefixEnd_6426166 := by exact prefixLift 6426166
  have htrace : WordTrace (prefixWord ++ tailWord_6426166) baseStart_6426166 baseEnd_6426166 := by
    simpa [prefixWord, tailWord_6426166, baseEnd_6426166] using wordTrace_append hprefix tailTrace_6426166
  have hstable : (prefixWord ++ tailWord_6426166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426166).length < 2 ^ (prefixWord ++ tailWord_6426166).sum := by decide
  have hdescent : baseEnd_6426166 < baseStart_6426166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426195 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 4, 2]
def baseStart_6426195 : Nat := 118140960795 + 6426195 * 2 ^ 59
def prefixEnd_6426195 : Nat := 4983230072969 + 3 ^ 40 * 6426195 * 2
def baseEnd_6426195 : Nat := 3299726814519590216208973

theorem tailTrace_6426195 : CollatzResearch.WordTrace tailWord_6426195 prefixEnd_6426195 3299726814519590216208973 := by
  unfold tailWord_6426195
  simp only [CollatzResearch.WordTrace]
  refine ⟨234382586954000496574136039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156255057969333664382757359 234382586954000496574136039)
  ·
    refine ⟨351573880431000744861204059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234382586954000496574136039 351573880431000744861204059)
    ·
      refine ⟨527360820646501117291806089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351573880431000744861204059 527360820646501117291806089)
      ·
        refine ⟨395520615484875837968854567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527360820646501117291806089 395520615484875837968854567)
        ·
          refine ⟨593280923227313756953281851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395520615484875837968854567 593280923227313756953281851)
          ·
            refine ⟨889921384840970635429922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593280923227313756953281851 889921384840970635429922777)
            ·
              refine ⟨667441038630727976572442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889921384840970635429922777 667441038630727976572442083)
              ·
                refine ⟨1001161557946091964858663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667441038630727976572442083 1001161557946091964858663125)
                ·
                  refine ⟨23464724014361530426374917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1001161557946091964858663125 23464724014361530426374917)
                  ·
                    refine ⟨4399635752692786954945297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23464724014361530426374917 4399635752692786954945297)
                    ·
                      refine ⟨3299726814519590216208973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399635752692786954945297 3299726814519590216208973)
                      ·
                        rfl

theorem cell23_6426195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4, 2].length) (baseStart_6426195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426195 prefixEnd_6426195 := by exact prefixLift 6426195
  have htrace : WordTrace (prefixWord ++ tailWord_6426195) baseStart_6426195 baseEnd_6426195 := by
    simpa [prefixWord, tailWord_6426195, baseEnd_6426195] using wordTrace_append hprefix tailTrace_6426195
  have hstable : (prefixWord ++ tailWord_6426195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426195).length < 2 ^ (prefixWord ++ tailWord_6426195).sum := by decide
  have hdescent : baseEnd_6426195 < baseStart_6426195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426199 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_6426199 : Nat := 118140960795 + 6426199 * 2 ^ 59
def prefixEnd_6426199 : Nat := 4983230072969 + 3 ^ 40 * 6426199 * 2
def baseEnd_6426199 : Nat := 3299728868442208200558955

theorem tailTrace_6426199 : CollatzResearch.WordTrace tailWord_6426199 prefixEnd_6426199 3299728868442208200558955 := by
  unfold tailWord_6426199
  simp only [CollatzResearch.WordTrace]
  refine ⟨234382732845986005257281651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156255155230657336838187767 234382732845986005257281651)
  ·
    refine ⟨351574099268979007885922477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234382732845986005257281651 351574099268979007885922477)
    ·
      refine ⟨131840287225867127957220929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351574099268979007885922477 131840287225867127957220929)
      ·
        refine ⟨98880215419400345967915697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131840287225867127957220929 98880215419400345967915697)
        ·
          refine ⟨74160161564550259475936773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98880215419400345967915697 74160161564550259475936773)
          ·
            refine ⟨13905030293353173651738145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74160161564550259475936773 13905030293353173651738145)
            ·
              refine ⟨10428772720014880238803609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13905030293353173651738145 10428772720014880238803609)
              ·
                refine ⟨7821579540011160179102707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10428772720014880238803609 7821579540011160179102707)
                ·
                  refine ⟨11732369310016740268654061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821579540011160179102707 11732369310016740268654061)
                  ·
                    refine ⟨4399638491256277600745273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11732369310016740268654061 4399638491256277600745273)
                    ·
                      refine ⟨3299728868442208200558955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399638491256277600745273 3299728868442208200558955)
                      ·
                        rfl

theorem cell23_6426199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_6426199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426199 prefixEnd_6426199 := by exact prefixLift 6426199
  have htrace : WordTrace (prefixWord ++ tailWord_6426199) baseStart_6426199 baseEnd_6426199 := by
    simpa [prefixWord, tailWord_6426199, baseEnd_6426199] using wordTrace_append hprefix tailTrace_6426199
  have hstable : (prefixWord ++ tailWord_6426199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426199).length < 2 ^ (prefixWord ++ tailWord_6426199).sum := by decide
  have hdescent : baseEnd_6426199 < baseStart_6426199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426245 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_6426245 : Nat := 118140960795 + 6426245 * 2 ^ 59
def prefixEnd_6426245 : Nat := 4983230072969 + 3 ^ 40 * 6426245 * 2
def baseEnd_6426245 : Nat := 3299752488552315020583743

theorem tailTrace_6426245 : CollatzResearch.WordTrace tailWord_6426245 prefixEnd_6426245 3299752488552315020583743 := by
  unfold tailWord_6426245
  simp only [CollatzResearch.WordTrace]
  refine ⟨234384410603819355113456189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156256273735879570075637459 234384410603819355113456189)
  ·
    refine ⟨87894153976432258167546071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234384410603819355113456189 87894153976432258167546071)
    ·
      refine ⟨131841230964648387251319107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87894153976432258167546071 131841230964648387251319107)
      ·
        refine ⟨197761846446972580876978661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131841230964648387251319107 197761846446972580876978661)
        ·
          refine ⟨37080346208807358914433499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197761846446972580876978661 37080346208807358914433499)
          ·
            refine ⟨55620519313211038371650249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37080346208807358914433499 55620519313211038371650249)
            ·
              refine ⟨41715389484908278778737687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55620519313211038371650249 41715389484908278778737687)
              ·
                refine ⟨62573084227362418168106531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41715389484908278778737687 62573084227362418168106531)
                ·
                  refine ⟨93859626341043627252159797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62573084227362418168106531 93859626341043627252159797)
                  ·
                    refine ⟨8799339969472840054889981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93859626341043627252159797 8799339969472840054889981)
                    ·
                      refine ⟨3299752488552315020583743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799339969472840054889981 3299752488552315020583743)
                      ·
                        rfl

theorem cell23_6426245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_6426245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426245 prefixEnd_6426245 := by exact prefixLift 6426245
  have htrace : WordTrace (prefixWord ++ tailWord_6426245) baseStart_6426245 baseEnd_6426245 := by
    simpa [prefixWord, tailWord_6426245, baseEnd_6426245] using wordTrace_append hprefix tailTrace_6426245
  have hstable : (prefixWord ++ tailWord_6426245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426245).length < 2 ^ (prefixWord ++ tailWord_6426245).sum := by decide
  have hdescent : baseEnd_6426245 < baseStart_6426245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426286 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_6426286 : Nat := 118140960795 + 6426286 * 2 ^ 59
def prefixEnd_6426286 : Nat := 4983230072969 + 3 ^ 40 * 6426286 * 2
def baseEnd_6426286 : Nat := 366641504584349928907895

theorem tailTrace_6426286 : CollatzResearch.WordTrace tailWord_6426286 prefixEnd_6426286 366641504584349928907895 := by
  unfold tailWord_6426286
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298238249583852389462339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156257270664447212743799141 29298238249583852389462339)
  ·
    refine ⟨43947357374375778584193509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29298238249583852389462339 43947357374375778584193509)
    ·
      refine ⟨8240129507695458484536283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43947357374375778584193509 8240129507695458484536283)
      ·
        refine ⟨12360194261543187726804425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240129507695458484536283 12360194261543187726804425)
        ·
          refine ⟨9270145696157390795103319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12360194261543187726804425 9270145696157390795103319)
          ·
            refine ⟨13905218544236086192654979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9270145696157390795103319 13905218544236086192654979)
            ·
              refine ⟨20857827816354129288982469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13905218544236086192654979 20857827816354129288982469)
              ·
                refine ⟨3910842715566399241684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20857827816354129288982469 3910842715566399241684213)
                ·
                  refine ⟨366641504584349928907895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910842715566399241684213 366641504584349928907895)
                  ·
                    rfl

theorem cell23_6426286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_6426286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426286 prefixEnd_6426286 := by exact prefixLift 6426286
  have htrace : WordTrace (prefixWord ++ tailWord_6426286) baseStart_6426286 baseEnd_6426286 := by
    simpa [prefixWord, tailWord_6426286, baseEnd_6426286] using wordTrace_append hprefix tailTrace_6426286
  have hstable : (prefixWord ++ tailWord_6426286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426286).length < 2 ^ (prefixWord ++ tailWord_6426286).sum := by decide
  have hdescent : baseEnd_6426286 < baseStart_6426286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426312 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_6426312 : Nat := 118140960795 + 6426312 * 2 ^ 59
def prefixEnd_6426312 : Nat := 4983230072969 + 3 ^ 40 * 6426312 * 2
def baseEnd_6426312 : Nat := 1099928963918722086148645

theorem tailTrace_6426312 : CollatzResearch.WordTrace tailWord_6426312 prefixEnd_6426312 1099928963918722086148645 := by
  unfold tailWord_6426312
  simp only [CollatzResearch.WordTrace]
  refine ⟨117193427147288312778072595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156257902863051083704096793 117193427147288312778072595)
  ·
    refine ⟨175790140720932469167108893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117193427147288312778072595 175790140720932469167108893)
    ·
      refine ⟨65921302770349675937665835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175790140720932469167108893 65921302770349675937665835)
      ·
        refine ⟨98881954155524513906498753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65921302770349675937665835 98881954155524513906498753)
        ·
          refine ⟨74161465616643385429874065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98881954155524513906498753 74161465616643385429874065)
          ·
            refine ⟨55621099212482539072405549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74161465616643385429874065 55621099212482539072405549)
            ·
              refine ⟨20857912204680952152152081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55621099212482539072405549 20857912204680952152152081)
              ·
                refine ⟨15643434153510714114114061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20857912204680952152152081 15643434153510714114114061)
                ·
                  refine ⟨5866287807566517792792773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15643434153510714114114061 5866287807566517792792773)
                  ·
                    refine ⟨1099928963918722086148645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5866287807566517792792773 1099928963918722086148645)
                    ·
                      rfl

theorem cell23_6426312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_6426312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426312 prefixEnd_6426312 := by exact prefixLift 6426312
  have htrace : WordTrace (prefixWord ++ tailWord_6426312) baseStart_6426312 baseEnd_6426312 := by
    simpa [prefixWord, tailWord_6426312, baseEnd_6426312] using wordTrace_append hprefix tailTrace_6426312
  have hstable : (prefixWord ++ tailWord_6426312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426312).length < 2 ^ (prefixWord ++ tailWord_6426312).sum := by decide
  have hdescent : baseEnd_6426312 < baseStart_6426312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426316 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_6426316 : Nat := 118140960795 + 6426316 * 2 ^ 59
def prefixEnd_6426316 : Nat := 4983230072969 + 3 ^ 40 * 6426316 * 2
def baseEnd_6426316 : Nat := 1099929648559594747598639

theorem tailTrace_6426316 : CollatzResearch.WordTrace tailWord_6426316 prefixEnd_6426316 1099929648559594747598639 := by
  unfold tailWord_6426316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117193500093281067119645401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156258000124374756159527201 117193500093281067119645401)
  ·
    refine ⟨87895125069960800339734051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117193500093281067119645401 87895125069960800339734051)
    ·
      refine ⟨131842687604941200509601077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87895125069960800339734051 131842687604941200509601077)
      ·
        refine ⟨12360251962963237547775101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131842687604941200509601077 12360251962963237547775101)
        ·
          refine ⟨4635094486111214080415663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12360251962963237547775101 4635094486111214080415663)
          ·
            refine ⟨6952641729166821120623495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635094486111214080415663 6952641729166821120623495)
            ·
              refine ⟨10428962593750231680935243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952641729166821120623495 10428962593750231680935243)
              ·
                refine ⟨15643443890625347521402865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428962593750231680935243 15643443890625347521402865)
                ·
                  refine ⟨11732582917969010641052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15643443890625347521402865 11732582917969010641052149)
                  ·
                    refine ⟨1099929648559594747598639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11732582917969010641052149 1099929648559594747598639)
                    ·
                      rfl

theorem cell23_6426316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_6426316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426316 prefixEnd_6426316 := by exact prefixLift 6426316
  have htrace : WordTrace (prefixWord ++ tailWord_6426316) baseStart_6426316 baseEnd_6426316 := by
    simpa [prefixWord, tailWord_6426316, baseEnd_6426316] using wordTrace_append hprefix tailTrace_6426316
  have hstable : (prefixWord ++ tailWord_6426316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426316).length < 2 ^ (prefixWord ++ tailWord_6426316).sum := by decide
  have hdescent : baseEnd_6426316 < baseStart_6426316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426329 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 1, 4]
def baseStart_6426329 : Nat := 118140960795 + 6426329 * 2 ^ 59
def prefixEnd_6426329 : Nat := 4983230072969 + 3 ^ 40 * 6426329 * 2
def baseEnd_6426329 : Nat := 1099931873642430897311119

theorem tailTrace_6426329 : CollatzResearch.WordTrace tailWord_6426329 prefixEnd_6426329 1099931873642430897311119 := by
  unfold tailWord_6426329
  simp only [CollatzResearch.WordTrace]
  refine ⟨234387474335515037459514041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156258316223676691639676027 234387474335515037459514041)
  ·
    refine ⟨175790605751636278094635531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234387474335515037459514041 175790605751636278094635531)
    ·
      refine ⟨263685908627454417141953297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175790605751636278094635531 263685908627454417141953297)
      ·
        refine ⟨197764431470590812856464973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263685908627454417141953297 197764431470590812856464973)
        ·
          refine ⟨74161661801471554821174365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197764431470590812856464973 74161661801471554821174365)
          ·
            refine ⟨27810623175551833057940387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74161661801471554821174365 27810623175551833057940387)
            ·
              refine ⟨41715934763327749586910581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27810623175551833057940387 41715934763327749586910581)
              ·
                refine ⟨3910868884061976523772867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41715934763327749586910581 3910868884061976523772867)
                ·
                  refine ⟨5866303326092964785659301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910868884061976523772867 5866303326092964785659301)
                  ·
                    refine ⟨1099931873642430897311119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5866303326092964785659301 1099931873642430897311119)
                    ·
                      rfl

theorem cell23_6426329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_6426329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426329 prefixEnd_6426329 := by exact prefixLift 6426329
  have htrace : WordTrace (prefixWord ++ tailWord_6426329) baseStart_6426329 baseEnd_6426329 := by
    simpa [prefixWord, tailWord_6426329, baseEnd_6426329] using wordTrace_append hprefix tailTrace_6426329
  have hstable : (prefixWord ++ tailWord_6426329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426329).length < 2 ^ (prefixWord ++ tailWord_6426329).sum := by decide
  have hdescent : baseEnd_6426329 < baseStart_6426329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426355 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 5, 5]
def baseStart_6426355 : Nat := 118140960795 + 6426355 * 2 ^ 59
def prefixEnd_6426355 : Nat := 4983230072969 + 3 ^ 40 * 6426355 * 2
def baseEnd_6426355 : Nat := 1099936323808103196736079

theorem tailTrace_6426355 : CollatzResearch.WordTrace tailWord_6426355 prefixEnd_6426355 1099936323808103196736079 := by
  unfold tailWord_6426355
  simp only [CollatzResearch.WordTrace]
  refine ⟨234388422633420843899960519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156258948422280562599973679 234388422633420843899960519)
  ·
    refine ⟨351582633950131265849940779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234388422633420843899960519 351582633950131265849940779)
    ·
      refine ⟨527373950925196898774911169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351582633950131265849940779 527373950925196898774911169)
      ·
        refine ⟨395530463193897674081183377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527373950925196898774911169 395530463193897674081183377)
        ·
          refine ⟨296647847395423255560887533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395530463193897674081183377 296647847395423255560887533)
          ·
            refine ⟨111242942773283720835332825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296647847395423255560887533 111242942773283720835332825)
            ·
              refine ⟨83432207079962790626499619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111242942773283720835332825 83432207079962790626499619)
              ·
                refine ⟨125148310619944185939749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83432207079962790626499619 125148310619944185939749429)
                ·
                  refine ⟨11732654120619767431851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125148310619944185939749429 11732654120619767431851509)
                  ·
                    refine ⟨1099936323808103196736079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11732654120619767431851509 1099936323808103196736079)
                    ·
                      rfl

theorem cell23_6426355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].length) (baseStart_6426355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426355 prefixEnd_6426355 := by exact prefixLift 6426355
  have htrace : WordTrace (prefixWord ++ tailWord_6426355) baseStart_6426355 baseEnd_6426355 := by
    simpa [prefixWord, tailWord_6426355, baseEnd_6426355] using wordTrace_append hprefix tailTrace_6426355
  have hstable : (prefixWord ++ tailWord_6426355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426355).length < 2 ^ (prefixWord ++ tailWord_6426355).sum := by decide
  have hdescent : baseEnd_6426355 < baseStart_6426355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426356 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6426356 : Nat := 118140960795 + 6426356 * 2 ^ 59
def prefixEnd_6426356 : Nat := 4983230072969 + 3 ^ 40 * 6426356 * 2
def baseEnd_6426356 : Nat := 3299809484904964086295733

theorem tailTrace_6426356 : CollatzResearch.WordTrace tailWord_6426356 prefixEnd_6426356 3299809484904964086295733 := by
  unfold tailWord_6426356
  simp only [CollatzResearch.WordTrace]
  refine ⟨117194229553208610535373461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156258972737611480713831281 117194229553208610535373461)
  ·
    refine ⟨5493479510306653618845631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117194229553208610535373461 5493479510306653618845631)
    ·
      refine ⟨8240219265459980428268447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493479510306653618845631 8240219265459980428268447)
      ·
        refine ⟨12360328898189970642402671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240219265459980428268447 12360328898189970642402671)
        ·
          refine ⟨18540493347284955963604007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12360328898189970642402671 18540493347284955963604007)
          ·
            refine ⟨27810740020927433945406011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18540493347284955963604007 27810740020927433945406011)
            ·
              refine ⟨41716110031391150918109017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27810740020927433945406011 41716110031391150918109017)
              ·
                refine ⟨31287082523543363188581763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41716110031391150918109017 31287082523543363188581763)
                ·
                  refine ⟨46930623785315044782872645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31287082523543363188581763 46930623785315044782872645)
                  ·
                    refine ⟨8799491959746570896788621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46930623785315044782872645 8799491959746570896788621)
                    ·
                      refine ⟨3299809484904964086295733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799491959746570896788621 3299809484904964086295733)
                      ·
                        rfl

theorem cell23_6426356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6426356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426356 prefixEnd_6426356 := by exact prefixLift 6426356
  have htrace : WordTrace (prefixWord ++ tailWord_6426356) baseStart_6426356 baseEnd_6426356 := by
    simpa [prefixWord, tailWord_6426356, baseEnd_6426356] using wordTrace_append hprefix tailTrace_6426356
  have hstable : (prefixWord ++ tailWord_6426356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426356).length < 2 ^ (prefixWord ++ tailWord_6426356).sum := by decide
  have hdescent : baseEnd_6426356 < baseStart_6426356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426369 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_6426369 : Nat := 118140960795 + 6426369 * 2 ^ 59
def prefixEnd_6426369 : Nat := 4983230072969 + 3 ^ 40 * 6426369 * 2
def baseEnd_6426369 : Nat := 3299816160153472535433173

theorem tailTrace_6426369 : CollatzResearch.WordTrace tailWord_6426369 prefixEnd_6426369 3299816160153472535433173 := by
  unfold tailWord_6426369
  simp only [CollatzResearch.WordTrace]
  refine ⟨234388933255370124290970161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156259288836913416193980107 234388933255370124290970161)
  ·
    refine ⟨175791699941527593218227621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234388933255370124290970161 175791699941527593218227621)
    ·
      refine ⟨32960943739036423728417679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175791699941527593218227621 32960943739036423728417679)
      ·
        refine ⟨49441415608554635592626519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32960943739036423728417679 49441415608554635592626519)
        ·
          refine ⟨74162123412831953388939779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49441415608554635592626519 74162123412831953388939779)
          ·
            refine ⟨111243185119247930083409669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74162123412831953388939779 111243185119247930083409669)
            ·
              refine ⟨20858097209858986890639313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111243185119247930083409669 20858097209858986890639313)
              ·
                refine ⟨15643572907394240167979485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20858097209858986890639313 15643572907394240167979485)
                ·
                  refine ⟨5866339840272840062992307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15643572907394240167979485 5866339840272840062992307)
                  ·
                    refine ⟨8799509760409260094488461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5866339840272840062992307 8799509760409260094488461)
                    ·
                      refine ⟨3299816160153472535433173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799509760409260094488461 3299816160153472535433173)
                      ·
                        rfl

theorem cell23_6426369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_6426369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426369 prefixEnd_6426369 := by exact prefixLift 6426369
  have htrace : WordTrace (prefixWord ++ tailWord_6426369) baseStart_6426369 baseEnd_6426369 := by
    simpa [prefixWord, tailWord_6426369, baseEnd_6426369] using wordTrace_append hprefix tailTrace_6426369
  have hstable : (prefixWord ++ tailWord_6426369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426369).length < 2 ^ (prefixWord ++ tailWord_6426369).sum := by decide
  have hdescent : baseEnd_6426369 < baseStart_6426369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426385 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_6426385 : Nat := 118140960795 + 6426385 * 2 ^ 59
def prefixEnd_6426385 : Nat := 4983230072969 + 3 ^ 40 * 6426385 * 2
def baseEnd_6426385 : Nat := 1099941458614648157611033

theorem tailTrace_6426385 : CollatzResearch.WordTrace tailWord_6426385 prefixEnd_6426385 1099941458614648157611033 := by
  unfold tailWord_6426385
  simp only [CollatzResearch.WordTrace]
  refine ⟨234389516823312159023552609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156259677882208106015701739 234389516823312159023552609)
  ·
    refine ⟨175792137617484119267664457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234389516823312159023552609 175792137617484119267664457)
    ·
      refine ⟨131844103213113089450748343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175792137617484119267664457 131844103213113089450748343)
      ·
        refine ⟨197766154819669634176122515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131844103213113089450748343 197766154819669634176122515)
        ·
          refine ⟨296649232229504451264183773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197766154819669634176122515 296649232229504451264183773)
          ·
            refine ⟨111243462086064169224068915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296649232229504451264183773 111243462086064169224068915)
            ·
              refine ⟨166865193129096253836103373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111243462086064169224068915 166865193129096253836103373)
              ·
                refine ⟨62574447423411095188538765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166865193129096253836103373 62574447423411095188538765)
                ·
                  refine ⟨23465417783779160695702037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62574447423411095188538765 23465417783779160695702037)
                  ·
                    refine ⟨1099941458614648157611033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23465417783779160695702037 1099941458614648157611033)
                    ·
                      rfl

theorem cell23_6426385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_6426385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426385 prefixEnd_6426385 := by exact prefixLift 6426385
  have htrace : WordTrace (prefixWord ++ tailWord_6426385) baseStart_6426385 baseEnd_6426385 := by
    simpa [prefixWord, tailWord_6426385, baseEnd_6426385] using wordTrace_append hprefix tailTrace_6426385
  have hstable : (prefixWord ++ tailWord_6426385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426385).length < 2 ^ (prefixWord ++ tailWord_6426385).sum := by decide
  have hdescent : baseEnd_6426385 < baseStart_6426385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_6426395 : Nat := 118140960795 + 6426395 * 2 ^ 59
def prefixEnd_6426395 : Nat := 4983230072969 + 3 ^ 40 * 6426395 * 2
def baseEnd_6426395 : Nat := 3299829510650489433708053

theorem tailTrace_6426395 : CollatzResearch.WordTrace tailWord_6426395 prefixEnd_6426395 3299829510650489433708053 := by
  unfold tailWord_6426395
  simp only [CollatzResearch.WordTrace]
  refine ⟨234389881553275930731416639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156259921035517287154277759 234389881553275930731416639)
  ·
    refine ⟨351584822329913896097124959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234389881553275930731416639 351584822329913896097124959)
    ·
      refine ⟨527377233494870844145687439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351584822329913896097124959 527377233494870844145687439)
      ·
        refine ⟨791065850242306266218531159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527377233494870844145687439 791065850242306266218531159)
        ·
          refine ⟨1186598775363459399327796739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791065850242306266218531159 1186598775363459399327796739)
          ·
            refine ⟨1779898163045189098991695109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186598775363459399327796739 1779898163045189098991695109)
            ·
              refine ⟨333730905570972956060942833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1779898163045189098991695109 333730905570972956060942833)
              ·
                refine ⟨250298179178229717045707125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333730905570972956060942833 250298179178229717045707125)
                ·
                  refine ⟨23465454297959035973035043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250298179178229717045707125 23465454297959035973035043)
                  ·
                    refine ⟨35198181446938553959552565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23465454297959035973035043 35198181446938553959552565)
                    ·
                      refine ⟨3299829510650489433708053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35198181446938553959552565 3299829510650489433708053)
                      ·
                        rfl

theorem cell23_6426395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_6426395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426395 prefixEnd_6426395 := by exact prefixLift 6426395
  have htrace : WordTrace (prefixWord ++ tailWord_6426395) baseStart_6426395 baseEnd_6426395 := by
    simpa [prefixWord, tailWord_6426395, baseEnd_6426395] using wordTrace_append hprefix tailTrace_6426395
  have hstable : (prefixWord ++ tailWord_6426395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426395).length < 2 ^ (prefixWord ++ tailWord_6426395).sum := by decide
  have hdescent : baseEnd_6426395 < baseStart_6426395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426412 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_6426412 : Nat := 118140960795 + 6426412 * 2 ^ 59
def prefixEnd_6426412 : Nat := 4983230072969 + 3 ^ 40 * 6426412 * 2
def baseEnd_6426412 : Nat := 3299838239821615867195475

theorem tailTrace_6426412 : CollatzResearch.WordTrace tailWord_6426412 prefixEnd_6426412 3299838239821615867195475 := by
  unfold tailWord_6426412
  simp only [CollatzResearch.WordTrace]
  refine ⟨117195250797107171317392745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156260334396142895089856993 117195250797107171317392745)
  ·
    refine ⟨87896438097830378488044559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117195250797107171317392745 87896438097830378488044559)
    ·
      refine ⟨131844657146745567732066839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87896438097830378488044559 131844657146745567732066839)
      ·
        refine ⟨197766985720118351598100259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131844657146745567732066839 197766985720118351598100259)
        ·
          refine ⟨296650478580177527397150389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197766985720118351598100259 296650478580177527397150389)
          ·
            refine ⟨27810982366891643193482849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296650478580177527397150389 27810982366891643193482849)
            ·
              refine ⟨20858236775168732395112137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27810982366891643193482849 20858236775168732395112137)
              ·
                refine ⟨15643677581376549296334103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20858236775168732395112137 15643677581376549296334103)
                ·
                  refine ⟨23465516372064823944501155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15643677581376549296334103 23465516372064823944501155)
                  ·
                    refine ⟨35198274558097235916751733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23465516372064823944501155 35198274558097235916751733)
                    ·
                      refine ⟨3299838239821615867195475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35198274558097235916751733 3299838239821615867195475)
                      ·
                        rfl

theorem cell23_6426412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_6426412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426412 prefixEnd_6426412 := by exact prefixLift 6426412
  have htrace : WordTrace (prefixWord ++ tailWord_6426412) baseStart_6426412 baseEnd_6426412 := by
    simpa [prefixWord, tailWord_6426412, baseEnd_6426412] using wordTrace_append hprefix tailTrace_6426412
  have hstable : (prefixWord ++ tailWord_6426412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426412).length < 2 ^ (prefixWord ++ tailWord_6426412).sum := by decide
  have hdescent : baseEnd_6426412 < baseStart_6426412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426426 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_6426426 : Nat := 118140960795 + 6426426 * 2 ^ 59
def prefixEnd_6426426 : Nat := 4983230072969 + 3 ^ 40 * 6426426 * 2
def baseEnd_6426426 : Nat := 3299845428550778812420411

theorem tailTrace_6426426 : CollatzResearch.WordTrace tailWord_6426426 prefixEnd_6426426 3299845428550778812420411 := by
  unfold tailWord_6426426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58597753054040905756448783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156260674810775748683863421 58597753054040905756448783)
  ·
    refine ⟨87896629581061358634673175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58597753054040905756448783 87896629581061358634673175)
    ·
      refine ⟨131844944371592037952009763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87896629581061358634673175 131844944371592037952009763)
      ·
        refine ⟨197767416557388056928014645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131844944371592037952009763 197767416557388056928014645)
        ·
          refine ⟨18540695302255130337001373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197767416557388056928014645 18540695302255130337001373)
          ·
            refine ⟨6952760738345673876375515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18540695302255130337001373 6952760738345673876375515)
            ·
              refine ⟨10429141107518510814563273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952760738345673876375515 10429141107518510814563273)
              ·
                refine ⟨7821855830638883110922455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10429141107518510814563273 7821855830638883110922455)
                ·
                  refine ⟨11732783745958324666383683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821855830638883110922455 11732783745958324666383683)
                  ·
                    refine ⟨17599175618937486999575525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11732783745958324666383683 17599175618937486999575525)
                    ·
                      refine ⟨3299845428550778812420411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17599175618937486999575525 3299845428550778812420411)
                      ·
                        rfl

theorem cell23_6426426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_6426426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426426 prefixEnd_6426426 := by exact prefixLift 6426426
  have htrace : WordTrace (prefixWord ++ tailWord_6426426) baseStart_6426426 baseEnd_6426426 := by
    simpa [prefixWord, tailWord_6426426, baseEnd_6426426] using wordTrace_append hprefix tailTrace_6426426
  have hstable : (prefixWord ++ tailWord_6426426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426426).length < 2 ^ (prefixWord ++ tailWord_6426426).sum := by decide
  have hdescent : baseEnd_6426426 < baseStart_6426426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426476 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_6426476 : Nat := 118140960795 + 6426476 * 2 ^ 59
def prefixEnd_6426476 : Nat := 4983230072969 + 3 ^ 40 * 6426476 * 2
def baseEnd_6426476 : Nat := 3299871102583503616795181

theorem tailTrace_6426476 : CollatzResearch.WordTrace tailWord_6426476 prefixEnd_6426476 3299871102583503616795181 := by
  unfold tailWord_6426476
  simp only [CollatzResearch.WordTrace]
  refine ⟨117196417932991240782557641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156261890577321654376743521 117196417932991240782557641)
  ·
    refine ⟨87897313449743430586918231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117196417932991240782557641 87897313449743430586918231)
    ·
      refine ⟨131845970174615145880377347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87897313449743430586918231 131845970174615145880377347)
      ·
        refine ⟨197768955261922718820566021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131845970174615145880377347 197768955261922718820566021)
        ·
          refine ⟨37081679111610509778856129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197768955261922718820566021 37081679111610509778856129)
          ·
            refine ⟨27811259333707882334142097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37081679111610509778856129 27811259333707882334142097)
            ·
              refine ⟨20858444500280911750606573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27811259333707882334142097 20858444500280911750606573)
              ·
                refine ⟨7821916687605341906477465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20858444500280911750606573 7821916687605341906477465)
                ·
                  refine ⟨5866437515704006429858099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821916687605341906477465 5866437515704006429858099)
                  ·
                    refine ⟨8799656273556009644787149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5866437515704006429858099 8799656273556009644787149)
                    ·
                      refine ⟨3299871102583503616795181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799656273556009644787149 3299871102583503616795181)
                      ·
                        rfl

theorem cell23_6426476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_6426476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426476 prefixEnd_6426476 := by exact prefixLift 6426476
  have htrace : WordTrace (prefixWord ++ tailWord_6426476) baseStart_6426476 baseEnd_6426476 := by
    simpa [prefixWord, tailWord_6426476, baseEnd_6426476] using wordTrace_append hprefix tailTrace_6426476
  have hstable : (prefixWord ++ tailWord_6426476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426476).length < 2 ^ (prefixWord ++ tailWord_6426476).sum := by decide
  have hdescent : baseEnd_6426476 < baseStart_6426476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426482 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6426482 : Nat := 118140960795 + 6426482 * 2 ^ 59
def prefixEnd_6426482 : Nat := 4983230072969 + 3 ^ 40 * 6426482 * 2
def baseEnd_6426482 : Nat := 3299874183467430593320153

theorem tailTrace_6426482 : CollatzResearch.WordTrace tailWord_6426482 prefixEnd_6426482 3299874183467430593320153 := by
  unfold tailWord_6426482
  simp only [CollatzResearch.WordTrace]
  refine ⟨58598263675990186147458425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156262036469307163059889133 58598263675990186147458425)
  ·
    refine ⟨43948697756992639610593819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58598263675990186147458425 43948697756992639610593819)
    ·
      refine ⟨65923046635488959415890729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43948697756992639610593819 65923046635488959415890729)
      ·
        refine ⟨49442284976616719561918047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65923046635488959415890729 49442284976616719561918047)
        ·
          refine ⟨74163427464925079342877071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49442284976616719561918047 74163427464925079342877071)
          ·
            refine ⟨111245141197387619014315607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74163427464925079342877071 111245141197387619014315607)
            ·
              refine ⟨166867711796081428521473411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111245141197387619014315607 166867711796081428521473411)
              ·
                refine ⟨250301567694122142782210117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166867711796081428521473411 250301567694122142782210117)
                ·
                  refine ⟨46931543942647901771664397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250301567694122142782210117 46931543942647901771664397)
                  ·
                    refine ⟨17599328978492963164374149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46931543942647901771664397 17599328978492963164374149)
                    ·
                      refine ⟨3299874183467430593320153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17599328978492963164374149 3299874183467430593320153)
                      ·
                        rfl

theorem cell23_6426482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6426482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426482 prefixEnd_6426482 := by exact prefixLift 6426482
  have htrace : WordTrace (prefixWord ++ tailWord_6426482) baseStart_6426482 baseEnd_6426482 := by
    simpa [prefixWord, tailWord_6426482, baseEnd_6426482] using wordTrace_append hprefix tailTrace_6426482
  have hstable : (prefixWord ++ tailWord_6426482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426482).length < 2 ^ (prefixWord ++ tailWord_6426482).sum := by decide
  have hdescent : baseEnd_6426482 < baseStart_6426482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426497 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6426497 : Nat := 118140960795 + 6426497 * 2 ^ 59
def prefixEnd_6426497 : Nat := 4983230072969 + 3 ^ 40 * 6426497 * 2
def baseEnd_6426497 : Nat := 3299881885677248034632585

theorem tailTrace_6426497 : CollatzResearch.WordTrace tailWord_6426497 prefixEnd_6426497 3299881885677248034632585 := by
  unfold tailWord_6426497
  simp only [CollatzResearch.WordTrace]
  refine ⟨234393601798906402151629745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156262401199270934767753163 234393601798906402151629745)
  ·
    refine ⟨175795201349179801613722309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234393601798906402151629745 175795201349179801613722309)
    ·
      refine ⟨32961600252971212802572933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175795201349179801613722309 32961600252971212802572933)
      ·
        refine ⟨6180300047432102400482425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32961600252971212802572933 6180300047432102400482425)
        ·
          refine ⟨4635225035574076800361819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180300047432102400482425 4635225035574076800361819)
          ·
            refine ⟨6952837553361115200542729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635225035574076800361819 6952837553361115200542729)
            ·
              refine ⟨5214628165020836400407047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952837553361115200542729 5214628165020836400407047)
              ·
                refine ⟨7821942247531254600610571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214628165020836400407047 7821942247531254600610571)
                ·
                  refine ⟨11732913371296881900915857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821942247531254600610571 11732913371296881900915857)
                  ·
                    refine ⟨8799685028472661425686893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11732913371296881900915857 8799685028472661425686893)
                    ·
                      refine ⟨3299881885677248034632585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799685028472661425686893 3299881885677248034632585)
                      ·
                        rfl

theorem cell23_6426497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6426497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426497 prefixEnd_6426497 := by exact prefixLift 6426497
  have htrace : WordTrace (prefixWord ++ tailWord_6426497) baseStart_6426497 baseEnd_6426497 := by
    simpa [prefixWord, tailWord_6426497, baseEnd_6426497] using wordTrace_append hprefix tailTrace_6426497
  have hstable : (prefixWord ++ tailWord_6426497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426497).length < 2 ^ (prefixWord ++ tailWord_6426497).sum := by decide
  have hdescent : baseEnd_6426497 < baseStart_6426497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426503 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_6426503 : Nat := 118140960795 + 6426503 * 2 ^ 59
def prefixEnd_6426503 : Nat := 4983230072969 + 3 ^ 40 * 6426503 * 2
def baseEnd_6426503 : Nat := 3299884966561175011157557

theorem tailTrace_6426503 : CollatzResearch.WordTrace tailWord_6426503 prefixEnd_6426503 3299884966561175011157557 := by
  unfold tailWord_6426503
  simp only [CollatzResearch.WordTrace]
  refine ⟨234393820636884665176348163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156262547091256443450898775 234393820636884665176348163)
  ·
    refine ⟨351590730955326997764522245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234393820636884665176348163 351590730955326997764522245)
    ·
      refine ⟨65923262054123812080847921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351590730955326997764522245 65923262054123812080847921)
      ·
        refine ⟨49442446540592859060635941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65923262054123812080847921 49442446540592859060635941)
        ·
          refine ⟨9270458726361161073869239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49442446540592859060635941 9270458726361161073869239)
          ·
            refine ⟨13905688089541741610803859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9270458726361161073869239 13905688089541741610803859)
            ·
              refine ⟨20858532134312612416205789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13905688089541741610803859 20858532134312612416205789)
              ·
                refine ⟨7821949550367229656077171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20858532134312612416205789 7821949550367229656077171)
                ·
                  refine ⟨11732924325550844484115757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821949550367229656077171 11732924325550844484115757)
                  ·
                    refine ⟨4399846622081566681543409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11732924325550844484115757 4399846622081566681543409)
                    ·
                      refine ⟨3299884966561175011157557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399846622081566681543409 3299884966561175011157557)
                      ·
                        rfl

theorem cell23_6426503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_6426503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426503 prefixEnd_6426503 := by exact prefixLift 6426503
  have htrace : WordTrace (prefixWord ++ tailWord_6426503) baseStart_6426503 baseEnd_6426503 := by
    simpa [prefixWord, tailWord_6426503, baseEnd_6426503] using wordTrace_append hprefix tailTrace_6426503
  have hstable : (prefixWord ++ tailWord_6426503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426503).length < 2 ^ (prefixWord ++ tailWord_6426503).sum := by decide
  have hdescent : baseEnd_6426503 < baseStart_6426503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426512 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_6426512 : Nat := 118140960795 + 6426512 * 2 ^ 59
def prefixEnd_6426512 : Nat := 4983230072969 + 3 ^ 40 * 6426512 * 2
def baseEnd_6426512 : Nat := 3299889587887065475945015

theorem tailTrace_6426512 : CollatzResearch.WordTrace tailWord_6426512 prefixEnd_6426512 3299889587887065475945015 := by
  unfold tailWord_6426512
  simp only [CollatzResearch.WordTrace]
  refine ⟨117197074446926029856712895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156262765929234706475617193 117197074446926029856712895)
  ·
    refine ⟨175795611670389044785069343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117197074446926029856712895 175795611670389044785069343)
    ·
      refine ⟨263693417505583567177604015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175795611670389044785069343 263693417505583567177604015)
      ·
        refine ⟨395540126258375350766406023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263693417505583567177604015 395540126258375350766406023)
        ·
          refine ⟨593310189387563026149609035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395540126258375350766406023 593310189387563026149609035)
          ·
            refine ⟨889965284081344539224413553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593310189387563026149609035 889965284081344539224413553)
            ·
              refine ⟨667473963061008404418310165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889965284081344539224413553 667473963061008404418310165)
              ·
                refine ⟨31287842018484768957108289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 667473963061008404418310165 31287842018484768957108289)
                ·
                  refine ⟨23465881513863576717831217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31287842018484768957108289 23465881513863576717831217)
                  ·
                    refine ⟨17599411135397682538373413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23465881513863576717831217 17599411135397682538373413)
                    ·
                      refine ⟨3299889587887065475945015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17599411135397682538373413 3299889587887065475945015)
                      ·
                        rfl

theorem cell23_6426512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_6426512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426512 prefixEnd_6426512 := by exact prefixLift 6426512
  have htrace : WordTrace (prefixWord ++ tailWord_6426512) baseStart_6426512 baseEnd_6426512 := by
    simpa [prefixWord, tailWord_6426512, baseEnd_6426512] using wordTrace_append hprefix tailTrace_6426512
  have hstable : (prefixWord ++ tailWord_6426512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426512).length < 2 ^ (prefixWord ++ tailWord_6426512).sum := by decide
  have hdescent : baseEnd_6426512 < baseStart_6426512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426552 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_6426552 : Nat := 118140960795 + 6426552 * 2 ^ 59
def prefixEnd_6426552 : Nat := 4983230072969 + 3 ^ 40 * 6426552 * 2
def baseEnd_6426552 : Nat := 1099970042371081773148277

theorem tailTrace_6426552 : CollatzResearch.WordTrace tailWord_6426552 prefixEnd_6426552 1099970042371081773148277 := by
  unfold tailWord_6426552
  simp only [CollatzResearch.WordTrace]
  refine ⟨117197803906853573272440955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156263738542471431029921273 117197803906853573272440955)
  ·
    refine ⟨175796705860280359908661433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117197803906853573272440955 175796705860280359908661433)
    ·
      refine ⟨131847529395210269931496075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175796705860280359908661433 131847529395210269931496075)
      ·
        refine ⟨197771294092815404897244113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131847529395210269931496075 197771294092815404897244113)
        ·
          refine ⟨148328470569611553672933085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197771294092815404897244113 148328470569611553672933085)
          ·
            refine ⟨55623176463604332627349907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148328470569611553672933085 55623176463604332627349907)
            ·
              refine ⟨83434764695406498941024861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55623176463604332627349907 83434764695406498941024861)
              ·
                refine ⟨31288036760777437102884323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83434764695406498941024861 31288036760777437102884323)
                ·
                  refine ⟨46932055141166155654326485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31288036760777437102884323 46932055141166155654326485)
                  ·
                    refine ⟨1099970042371081773148277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46932055141166155654326485 1099970042371081773148277)
                    ·
                      rfl

theorem cell23_6426552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_6426552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426552 prefixEnd_6426552 := by exact prefixLift 6426552
  have htrace : WordTrace (prefixWord ++ tailWord_6426552) baseStart_6426552 baseEnd_6426552 := by
    simpa [prefixWord, tailWord_6426552, baseEnd_6426552] using wordTrace_append hprefix tailTrace_6426552
  have hstable : (prefixWord ++ tailWord_6426552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426552).length < 2 ^ (prefixWord ++ tailWord_6426552).sum := by decide
  have hdescent : baseEnd_6426552 < baseStart_6426552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426592 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6426592 : Nat := 118140960795 + 6426592 * 2 ^ 59
def prefixEnd_6426592 : Nat := 4983230072969 + 3 ^ 40 * 6426592 * 2
def baseEnd_6426592 : Nat := 3299930666339425162944647

theorem tailTrace_6426592 : CollatzResearch.WordTrace tailWord_6426592 prefixEnd_6426592 3299930666339425162944647 := by
  unfold tailWord_6426592
  simp only [CollatzResearch.WordTrace]
  refine ⟨117198533366781116688169015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156264711155708155584225353 117198533366781116688169015)
  ·
    refine ⟨175797800050171675032253523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117198533366781116688169015 175797800050171675032253523)
    ·
      refine ⟨263696700075257512548380285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175797800050171675032253523 263696700075257512548380285)
      ·
        refine ⟨98886262528221567205642607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263696700075257512548380285 98886262528221567205642607)
        ·
          refine ⟨148329393792332350808463911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98886262528221567205642607 148329393792332350808463911)
          ·
            refine ⟨222494090688498526212695867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148329393792332350808463911 222494090688498526212695867)
            ·
              refine ⟨333741136032747789319043801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222494090688498526212695867 333741136032747789319043801)
              ·
                refine ⟨250305852024560841989282851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333741136032747789319043801 250305852024560841989282851)
                ·
                  refine ⟨375458778036841262983924277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250305852024560841989282851 375458778036841262983924277)
                  ·
                    refine ⟨35199260440953868404742901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 375458778036841262983924277 35199260440953868404742901)
                    ·
                      refine ⟨3299930666339425162944647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35199260440953868404742901 3299930666339425162944647)
                      ·
                        rfl

theorem cell23_6426592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6426592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426592 prefixEnd_6426592 := by exact prefixLift 6426592
  have htrace : WordTrace (prefixWord ++ tailWord_6426592) baseStart_6426592 baseEnd_6426592 := by
    simpa [prefixWord, tailWord_6426592, baseEnd_6426592] using wordTrace_append hprefix tailTrace_6426592
  have hstable : (prefixWord ++ tailWord_6426592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426592).length < 2 ^ (prefixWord ++ tailWord_6426592).sum := by decide
  have hdescent : baseEnd_6426592 < baseStart_6426592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426606 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6426606 : Nat := 118140960795 + 6426606 * 2 ^ 59
def prefixEnd_6426606 : Nat := 4983230072969 + 3 ^ 40 * 6426606 * 2
def baseEnd_6426606 : Nat := 3299937855068588108169583

theorem tailTrace_6426606 : CollatzResearch.WordTrace tailWord_6426606 prefixEnd_6426606 3299937855068588108169583 := by
  unfold tailWord_6426606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29299697169438939220918459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156265051570341009178231781 29299697169438939220918459)
  ·
    refine ⟨43949545754158408831377689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29299697169438939220918459 43949545754158408831377689)
    ·
      refine ⟨32962159315618806623533267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43949545754158408831377689 32962159315618806623533267)
      ·
        refine ⟨49443238973428209935299901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32962159315618806623533267 49443238973428209935299901)
        ·
          refine ⟨18541214615035578725737463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49443238973428209935299901 18541214615035578725737463)
          ·
            refine ⟨27811821922553368088606195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541214615035578725737463 27811821922553368088606195)
            ·
              refine ⟨41717732883830052132909293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27811821922553368088606195 41717732883830052132909293)
              ·
                refine ⟨15644149831436269549840985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41717732883830052132909293 15644149831436269549840985)
                ·
                  refine ⟨11733112373577202162380739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15644149831436269549840985 11733112373577202162380739)
                  ·
                    refine ⟨17599668560365803243571109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11733112373577202162380739 17599668560365803243571109)
                    ·
                      refine ⟨3299937855068588108169583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17599668560365803243571109 3299937855068588108169583)
                      ·
                        rfl

theorem cell23_6426606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6426606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426606 prefixEnd_6426606 := by exact prefixLift 6426606
  have htrace : WordTrace (prefixWord ++ tailWord_6426606) baseStart_6426606 baseEnd_6426606 := by
    simpa [prefixWord, tailWord_6426606, baseEnd_6426606] using wordTrace_append hprefix tailTrace_6426606
  have hstable : (prefixWord ++ tailWord_6426606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426606).length < 2 ^ (prefixWord ++ tailWord_6426606).sum := by decide
  have hdescent : baseEnd_6426606 < baseStart_6426606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426629 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 6]
def baseStart_6426629 : Nat := 118140960795 + 6426629 * 2 ^ 59
def prefixEnd_6426629 : Nat := 4983230072969 + 3 ^ 40 * 6426629 * 2
def baseEnd_6426629 : Nat := 366661073902626835353553

theorem tailTrace_6426629 : CollatzResearch.WordTrace tailWord_6426629 prefixEnd_6426629 366661073902626835353553 := by
  unfold tailWord_6426629
  simp only [CollatzResearch.WordTrace]
  refine ⟨234398416234428188695434941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156265610822952125796956627 234398416234428188695434941)
  ·
    refine ⟨87899406087910570760788103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234398416234428188695434941 87899406087910570760788103)
    ·
      refine ⟨131849109131865856141182155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87899406087910570760788103 131849109131865856141182155)
      ·
        refine ⟨197773663697798784211773233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131849109131865856141182155 197773663697798784211773233)
        ·
          refine ⟨148330247773349088158829925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197773663697798784211773233 148330247773349088158829925)
          ·
            refine ⟨27811921457502954029780611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148330247773349088158829925 27811921457502954029780611)
            ·
              refine ⟨41717882186254431044670917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27811921457502954029780611 41717882186254431044670917)
              ·
                refine ⟨7822102909922705820875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41717882186254431044670917 7822102909922705820875797)
                ·
                  refine ⟨366661073902626835353553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7822102909922705820875797 366661073902626835353553)
                  ·
                    rfl

theorem cell23_6426629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_6426629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426629 prefixEnd_6426629 := by exact prefixLift 6426629
  have htrace : WordTrace (prefixWord ++ tailWord_6426629) baseStart_6426629 baseEnd_6426629 := by
    simpa [prefixWord, tailWord_6426629, baseEnd_6426629] using wordTrace_append hprefix tailTrace_6426629
  have hstable : (prefixWord ++ tailWord_6426629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426629).length < 2 ^ (prefixWord ++ tailWord_6426629).sum := by decide
  have hdescent : baseEnd_6426629 < baseStart_6426629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426659 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 3, 5]
def baseStart_6426659 : Nat := 118140960795 + 6426659 * 2 ^ 59
def prefixEnd_6426659 : Nat := 4983230072969 + 3 ^ 40 * 6426659 * 2
def baseEnd_6426659 : Nat := 1099988356514425466935613

theorem tailTrace_6426659 : CollatzResearch.WordTrace tailWord_6426659 prefixEnd_6426659 1099988356514425466935613 := by
  unfold tailWord_6426659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234399510424319503819027031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156266340282879669212684687 234399510424319503819027031)
  ·
    refine ⟨351599265636479255728540547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234399510424319503819027031 351599265636479255728540547)
    ·
      refine ⟨527398898454718883592810821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351599265636479255728540547 527398898454718883592810821)
      ·
        refine ⟨98887293460259790673652029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 527398898454718883592810821 98887293460259790673652029)
        ·
          refine ⟨37082735047597421502619511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98887293460259790673652029 37082735047597421502619511)
          ·
            refine ⟨55624102571396132253929267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37082735047597421502619511 55624102571396132253929267)
            ·
              refine ⟨83436153857094198380893901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55624102571396132253929267 83436153857094198380893901)
              ·
                refine ⟨31288557696410324392835213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83436153857094198380893901 31288557696410324392835213)
                ·
                  refine ⟨11733209136153871647313205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31288557696410324392835213 11733209136153871647313205)
                  ·
                    refine ⟨1099988356514425466935613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11733209136153871647313205 1099988356514425466935613)
                    ·
                      rfl

theorem cell23_6426659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].length) (baseStart_6426659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426659 prefixEnd_6426659 := by exact prefixLift 6426659
  have htrace : WordTrace (prefixWord ++ tailWord_6426659) baseStart_6426659 baseEnd_6426659 := by
    simpa [prefixWord, tailWord_6426659, baseEnd_6426659] using wordTrace_append hprefix tailTrace_6426659
  have hstable : (prefixWord ++ tailWord_6426659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426659).length < 2 ^ (prefixWord ++ tailWord_6426659).sum := by decide
  have hdescent : baseEnd_6426659 < baseStart_6426659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426660 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6426660 : Nat := 118140960795 + 6426660 * 2 ^ 59
def prefixEnd_6426660 : Nat := 4983230072969 + 3 ^ 40 * 6426660 * 2
def baseEnd_6426660 : Nat := 3299965583023930896894335

theorem tailTrace_6426660 : CollatzResearch.WordTrace tailWord_6426660 prefixEnd_6426660 3299965583023930896894335 := by
  unfold tailWord_6426660
  simp only [CollatzResearch.WordTrace]
  refine ⟨117199773448657940494906717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156266364598210587326542289 117199773448657940494906717)
  ·
    refine ⟨43949915043246727685590019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117199773448657940494906717 43949915043246727685590019)
    ·
      refine ⟨65924872564870091528385029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43949915043246727685590019 65924872564870091528385029)
      ·
        refine ⟨12360913605913142161572193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65924872564870091528385029 12360913605913142161572193)
        ·
          refine ⟨9270685204434856621179145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12360913605913142161572193 9270685204434856621179145)
          ·
            refine ⟨6953013903326142465884359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9270685204434856621179145 6953013903326142465884359)
            ·
              refine ⟨10429520854989213698826539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953013903326142465884359 10429520854989213698826539)
              ·
                refine ⟨15644281282483820548239809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10429520854989213698826539 15644281282483820548239809)
                ·
                  refine ⟨11733210961862865411179857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15644281282483820548239809 11733210961862865411179857)
                  ·
                    refine ⟨8799908221397149058384893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11733210961862865411179857 8799908221397149058384893)
                    ·
                      refine ⟨3299965583023930896894335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8799908221397149058384893 3299965583023930896894335)
                      ·
                        rfl

theorem cell23_6426660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6426660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426660 prefixEnd_6426660 := by exact prefixLift 6426660
  have htrace : WordTrace (prefixWord ++ tailWord_6426660) baseStart_6426660 baseEnd_6426660 := by
    simpa [prefixWord, tailWord_6426660, baseEnd_6426660] using wordTrace_append hprefix tailTrace_6426660
  have hstable : (prefixWord ++ tailWord_6426660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426660).length < 2 ^ (prefixWord ++ tailWord_6426660).sum := by decide
  have hdescent : baseEnd_6426660 < baseStart_6426660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426699 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_6426699 : Nat := 118140960795 + 6426699 * 2 ^ 59
def prefixEnd_6426699 : Nat := 4983230072969 + 3 ^ 40 * 6426699 * 2
def baseEnd_6426699 : Nat := 3299985608769456244306655

theorem tailTrace_6426699 : CollatzResearch.WordTrace tailWord_6426699 prefixEnd_6426699 3299985608769456244306655 := by
  unfold tailWord_6426699
  simp only [CollatzResearch.WordTrace]
  refine ⟨234400969344174590650483151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156267312896116393766988767 234400969344174590650483151)
  ·
    refine ⟨351601454016261885975724727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234400969344174590650483151 351601454016261885975724727)
    ·
      refine ⟨527402181024392828963587091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351601454016261885975724727 527402181024392828963587091)
      ·
        refine ⟨791103271536589243445380637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527402181024392828963587091 791103271536589243445380637)
        ·
          refine ⟨296663726826220966292017739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791103271536589243445380637 296663726826220966292017739)
          ·
            refine ⟨444995590239331449438026609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296663726826220966292017739 444995590239331449438026609)
            ·
              refine ⟨333746692679498587078519957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444995590239331449438026609 333746692679498587078519957)
              ·
                refine ⟨15644376219351496269305623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333746692679498587078519957 15644376219351496269305623)
                ·
                  refine ⟨23466564329027244403958435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644376219351496269305623 23466564329027244403958435)
                  ·
                    refine ⟨35199846493540866605937653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23466564329027244403958435 35199846493540866605937653)
                    ·
                      refine ⟨3299985608769456244306655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35199846493540866605937653 3299985608769456244306655)
                      ·
                        rfl

theorem cell23_6426699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_6426699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426699 prefixEnd_6426699 := by exact prefixLift 6426699
  have htrace : WordTrace (prefixWord ++ tailWord_6426699) baseStart_6426699 baseEnd_6426699 := by
    simpa [prefixWord, tailWord_6426699, baseEnd_6426699] using wordTrace_append hprefix tailTrace_6426699
  have hstable : (prefixWord ++ tailWord_6426699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426699).length < 2 ^ (prefixWord ++ tailWord_6426699).sum := by decide
  have hdescent : baseEnd_6426699 < baseStart_6426699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426710 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6426710 : Nat := 118140960795 + 6426710 * 2 ^ 59
def prefixEnd_6426710 : Nat := 4983230072969 + 3 ^ 40 * 6426710 * 2
def baseEnd_6426710 : Nat := 1099997085685551900423035

theorem tailTrace_6426710 : CollatzResearch.WordTrace tailWord_6426710 prefixEnd_6426710 1099997085685551900423035 := by
  unfold tailWord_6426710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650085659195921220570849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156267580364756493019422389 14650085659195921220570849)
  ·
    refine ⟨10987564244396940915428137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14650085659195921220570849 10987564244396940915428137)
    ·
      refine ⟨8240673183297705686571103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10987564244396940915428137 8240673183297705686571103)
      ·
        refine ⟨12361009774946558529856655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240673183297705686571103 12361009774946558529856655)
        ·
          refine ⟨18541514662419837794784983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12361009774946558529856655 18541514662419837794784983)
          ·
            refine ⟨27812271993629756692177475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541514662419837794784983 27812271993629756692177475)
            ·
              refine ⟨41718407990444635038266213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812271993629756692177475 41718407990444635038266213)
              ·
                refine ⟨7822201498208369069674915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41718407990444635038266213 7822201498208369069674915)
                ·
                  refine ⟨11733302247312553604512373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822201498208369069674915 11733302247312553604512373)
                  ·
                    refine ⟨1099997085685551900423035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11733302247312553604512373 1099997085685551900423035)
                    ·
                      rfl

theorem cell23_6426710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6426710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426710 prefixEnd_6426710 := by exact prefixLift 6426710
  have htrace : WordTrace (prefixWord ++ tailWord_6426710) baseStart_6426710 baseEnd_6426710 := by
    simpa [prefixWord, tailWord_6426710, baseEnd_6426710] using wordTrace_append hprefix tailTrace_6426710
  have hstable : (prefixWord ++ tailWord_6426710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426710).length < 2 ^ (prefixWord ++ tailWord_6426710).sum := by decide
  have hdescent : baseEnd_6426710 < baseStart_6426710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426713 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 3, 2, 2]
def baseStart_6426713 : Nat := 118140960795 + 6426713 * 2 ^ 59
def prefixEnd_6426713 : Nat := 4983230072969 + 3 ^ 40 * 6426713 * 2
def baseEnd_6426713 : Nat := 3299992797498619189531591

theorem tailTrace_6426713 : CollatzResearch.WordTrace tailWord_6426713 prefixEnd_6426713 3299992797498619189531591 := by
  unfold tailWord_6426713
  simp only [CollatzResearch.WordTrace]
  refine ⟨234401479966123871041492793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156267653310749247360995195 234401479966123871041492793)
  ·
    refine ⟨175801109974592903281119595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234401479966123871041492793 175801109974592903281119595)
    ·
      refine ⟨263701664961889354921679393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175801109974592903281119595 263701664961889354921679393)
      ·
        refine ⟨197776248721417016191259545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263701664961889354921679393 197776248721417016191259545)
        ·
          refine ⟨148332186541062762143444659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197776248721417016191259545 148332186541062762143444659)
          ·
            refine ⟨222498279811594143215166989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148332186541062762143444659 222498279811594143215166989)
            ·
              refine ⟨83436854929347803705687621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222498279811594143215166989 83436854929347803705687621)
              ·
                refine ⟨15644410299252713194816429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83436854929347803705687621 15644410299252713194816429)
                ·
                  refine ⟨5866653862219767448056161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15644410299252713194816429 5866653862219767448056161)
                  ·
                    refine ⟨4399990396664825586042121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5866653862219767448056161 4399990396664825586042121)
                    ·
                      refine ⟨3299992797498619189531591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4399990396664825586042121 3299992797498619189531591)
                      ·
                        rfl

theorem cell23_6426713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_6426713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426713 prefixEnd_6426713 := by exact prefixLift 6426713
  have htrace : WordTrace (prefixWord ++ tailWord_6426713) baseStart_6426713 baseEnd_6426713 := by
    simpa [prefixWord, tailWord_6426713, baseEnd_6426713] using wordTrace_append hprefix tailTrace_6426713
  have hstable : (prefixWord ++ tailWord_6426713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426713).length < 2 ^ (prefixWord ++ tailWord_6426713).sum := by decide
  have hdescent : baseEnd_6426713 < baseStart_6426713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426733 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6426733 : Nat := 118140960795 + 6426733 * 2 ^ 59
def prefixEnd_6426733 : Nat := 4983230072969 + 3 ^ 40 * 6426733 * 2
def baseEnd_6426733 : Nat := 3300003067111709111281499

theorem tailTrace_6426733 : CollatzResearch.WordTrace tailWord_6426733 prefixEnd_6426733 3300003067111709111281499 := by
  unfold tailWord_6426733
  simp only [CollatzResearch.WordTrace]
  refine ⟨234402209426051414457220853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156268139617367609638147235 234402209426051414457220853)
  ·
    refine ⟨21975207133692320105364455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234402209426051414457220853 21975207133692320105364455)
    ·
      refine ⟨32962810700538480158046683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21975207133692320105364455 32962810700538480158046683)
      ·
        refine ⟨49444216050807720237070025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32962810700538480158046683 49444216050807720237070025)
        ·
          refine ⟨37083162038105790177802519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49444216050807720237070025 37083162038105790177802519)
          ·
            refine ⟨55624743057158685266703779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37083162038105790177802519 55624743057158685266703779)
            ·
              refine ⟨83437114585738027900055669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55624743057158685266703779 83437114585738027900055669)
              ·
                refine ⟨7822229492412940115630219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83437114585738027900055669 7822229492412940115630219)
                ·
                  refine ⟨11733344238619410173445329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822229492412940115630219 11733344238619410173445329)
                  ·
                    refine ⟨8800008178964557630083997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11733344238619410173445329 8800008178964557630083997)
                    ·
                      refine ⟨3300003067111709111281499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800008178964557630083997 3300003067111709111281499)
                      ·
                        rfl

theorem cell23_6426733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6426733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426733 prefixEnd_6426733 := by exact prefixLift 6426733
  have htrace : WordTrace (prefixWord ++ tailWord_6426733) baseStart_6426733 baseEnd_6426733 := by
    simpa [prefixWord, tailWord_6426733, baseEnd_6426733] using wordTrace_append hprefix tailTrace_6426733
  have hstable : (prefixWord ++ tailWord_6426733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426733).length < 2 ^ (prefixWord ++ tailWord_6426733).sum := by decide
  have hdescent : baseEnd_6426733 < baseStart_6426733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426773 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_6426773 : Nat := 118140960795 + 6426773 * 2 ^ 59
def prefixEnd_6426773 : Nat := 4983230072969 + 3 ^ 40 * 6426773 * 2
def baseEnd_6426773 : Nat := 3300023606337888954781315

theorem tailTrace_6426773 : CollatzResearch.WordTrace tailWord_6426773 prefixEnd_6426773 3300023606337888954781315 := by
  unfold tailWord_6426773
  simp only [CollatzResearch.WordTrace]
  refine ⟨234403668345906501288676973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156269112230604334192451315 234403668345906501288676973)
  ·
    refine ⟨87901375629714937983253865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234403668345906501288676973 87901375629714937983253865)
    ·
      refine ⟨65926031722286203487440399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87901375629714937983253865 65926031722286203487440399)
      ·
        refine ⟨98889047583429305231160599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65926031722286203487440399 98889047583429305231160599)
        ·
          refine ⟨148333571375143957846740899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98889047583429305231160599 148333571375143957846740899)
          ·
            refine ⟨222500357062715936770111349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148333571375143957846740899 222500357062715936770111349)
            ·
              refine ⟨20859408474629619072197939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222500357062715936770111349 20859408474629619072197939)
              ·
                refine ⟨31289112711944428608296909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20859408474629619072197939 31289112711944428608296909)
                ·
                  refine ⟨11733417266979160728111341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31289112711944428608296909 11733417266979160728111341)
                  ·
                    refine ⟨4400031475117185273041753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11733417266979160728111341 4400031475117185273041753)
                    ·
                      refine ⟨3300023606337888954781315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400031475117185273041753 3300023606337888954781315)
                      ·
                        rfl

theorem cell23_6426773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_6426773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426773 prefixEnd_6426773 := by exact prefixLift 6426773
  have htrace : WordTrace (prefixWord ++ tailWord_6426773) baseStart_6426773 baseEnd_6426773 := by
    simpa [prefixWord, tailWord_6426773, baseEnd_6426773] using wordTrace_append hprefix tailTrace_6426773
  have hstable : (prefixWord ++ tailWord_6426773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426773).length < 2 ^ (prefixWord ++ tailWord_6426773).sum := by decide
  have hdescent : baseEnd_6426773 < baseStart_6426773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426774 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6426774 : Nat := 118140960795 + 6426774 * 2 ^ 59
def prefixEnd_6426774 : Nat := 4983230072969 + 3 ^ 40 * 6426774 * 2
def baseEnd_6426774 : Nat := 1100008039939514483622937

theorem tailTrace_6426774 : CollatzResearch.WordTrace tailWord_6426774 prefixEnd_6426774 1100008039939514483622937 := by
  unfold tailWord_6426774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650231551181429903716461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156269136545935252306308917 14650231551181429903716461)
  ·
    refine ⟨5493836831693036213893673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14650231551181429903716461 5493836831693036213893673)
    ·
      refine ⟨4120377623769777160420255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493836831693036213893673 4120377623769777160420255)
      ·
        refine ⟨6180566435654665740630383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120377623769777160420255 6180566435654665740630383)
        ·
          refine ⟨9270849653481998610945575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180566435654665740630383 9270849653481998610945575)
          ·
            refine ⟨13906274480222997916418363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9270849653481998610945575 13906274480222997916418363)
            ·
              refine ⟨20859411720334496874627545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13906274480222997916418363 20859411720334496874627545)
              ·
                refine ⟨15644558790250872655970659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20859411720334496874627545 15644558790250872655970659)
                ·
                  refine ⟨23466838185376308983955989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644558790250872655970659 23466838185376308983955989)
                  ·
                    refine ⟨1100008039939514483622937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23466838185376308983955989 1100008039939514483622937)
                    ·
                      rfl

theorem cell23_6426774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6426774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426774 prefixEnd_6426774 := by exact prefixLift 6426774
  have htrace : WordTrace (prefixWord ++ tailWord_6426774) baseStart_6426774 baseEnd_6426774 := by
    simpa [prefixWord, tailWord_6426774, baseEnd_6426774] using wordTrace_append hprefix tailTrace_6426774
  have hstable : (prefixWord ++ tailWord_6426774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426774).length < 2 ^ (prefixWord ++ tailWord_6426774).sum := by decide
  have hdescent : baseEnd_6426774 < baseStart_6426774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426797 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_6426797 : Nat := 118140960795 + 6426797 * 2 ^ 59
def prefixEnd_6426797 : Nat := 4983230072969 + 3 ^ 40 * 6426797 * 2
def baseEnd_6426797 : Nat := 3300035929873596860881205

theorem tailTrace_6426797 : CollatzResearch.WordTrace tailWord_6426797 prefixEnd_6426797 3300035929873596860881205 := by
  unfold tailWord_6426797
  simp only [CollatzResearch.WordTrace]
  refine ⟨234404543697819553387550645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156269695798546368925033763 234404543697819553387550645)
  ·
    refine ⟨21975425971670583130082873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234404543697819553387550645 21975425971670583130082873)
    ·
      refine ⟨16481569478752937347562155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21975425971670583130082873 16481569478752937347562155)
      ·
        refine ⟨24722354218129406021343233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16481569478752937347562155 24722354218129406021343233)
        ·
          refine ⟨18541765663597054516007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24722354218129406021343233 18541765663597054516007425)
          ·
            refine ⟨13906324247697790887005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18541765663597054516007425 13906324247697790887005569)
            ·
              refine ⟨10429743185773343165254177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13906324247697790887005569 10429743185773343165254177)
              ·
                refine ⟨7822307389330007373940633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10429743185773343165254177 7822307389330007373940633)
                ·
                  refine ⟨5866730541997505530455475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7822307389330007373940633 5866730541997505530455475)
                  ·
                    refine ⟨8800095812996258295683213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5866730541997505530455475 8800095812996258295683213)
                    ·
                      refine ⟨3300035929873596860881205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800095812996258295683213 3300035929873596860881205)
                      ·
                        rfl

theorem cell23_6426797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_6426797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426797 prefixEnd_6426797 := by exact prefixLift 6426797
  have htrace : WordTrace (prefixWord ++ tailWord_6426797) baseStart_6426797 baseEnd_6426797 := by
    simpa [prefixWord, tailWord_6426797, baseEnd_6426797] using wordTrace_append hprefix tailTrace_6426797
  have hstable : (prefixWord ++ tailWord_6426797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426797).length < 2 ^ (prefixWord ++ tailWord_6426797).sum := by decide
  have hdescent : baseEnd_6426797 < baseStart_6426797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426799 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_6426799 : Nat := 118140960795 + 6426799 * 2 ^ 59
def prefixEnd_6426799 : Nat := 4983230072969 + 3 ^ 40 * 6426799 * 2
def baseEnd_6426799 : Nat := 3300036956834905853056195

theorem tailTrace_6426799 : CollatzResearch.WordTrace tailWord_6426799 prefixEnd_6426799 3300036956834905853056195 := by
  unfold tailWord_6426799
  simp only [CollatzResearch.WordTrace]
  refine ⟨234404616643812307729123451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156269744429208205152748967 234404616643812307729123451)
  ·
    refine ⟨351606924965718461593685177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234404616643812307729123451 351606924965718461593685177)
    ·
      refine ⟨263705193724288846195263883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351606924965718461593685177 263705193724288846195263883)
      ·
        refine ⟨395557790586433269292895825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263705193724288846195263883 395557790586433269292895825)
        ·
          refine ⟨296668342939824951969671869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395557790586433269292895825 296668342939824951969671869)
          ·
            refine ⟨111250628602434356988626951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296668342939824951969671869 111250628602434356988626951)
            ·
              refine ⟨166875942903651535482940427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111250628602434356988626951 166875942903651535482940427)
              ·
                refine ⟨250313914355477303224410641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166875942903651535482940427 250313914355477303224410641)
                ·
                  refine ⟨187735435766607977418307981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250313914355477303224410641 187735435766607977418307981)
                  ·
                    refine ⟨70400788412477991531865493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187735435766607977418307981 70400788412477991531865493)
                    ·
                      refine ⟨3300036956834905853056195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70400788412477991531865493 3300036956834905853056195)
                      ·
                        rfl

theorem cell23_6426799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_6426799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426799 prefixEnd_6426799 := by exact prefixLift 6426799
  have htrace : WordTrace (prefixWord ++ tailWord_6426799) baseStart_6426799 baseEnd_6426799 := by
    simpa [prefixWord, tailWord_6426799, baseEnd_6426799] using wordTrace_append hprefix tailTrace_6426799
  have hstable : (prefixWord ++ tailWord_6426799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426799).length < 2 ^ (prefixWord ++ tailWord_6426799).sum := by decide
  have hdescent : baseEnd_6426799 < baseStart_6426799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426804 : List Nat := [2, 5, 3, 1, 2, 1, 1, 8]
def baseStart_6426804 : Nat := 118140960795 + 6426804 * 2 ^ 59
def prefixEnd_6426804 : Nat := 4983230072969 + 3 ^ 40 * 6426804 * 2
def baseEnd_6426804 : Nat := 122223686082895493833099

theorem tailTrace_6426804 : CollatzResearch.WordTrace tailWord_6426804 prefixEnd_6426804 122223686082895493833099 := by
  unfold tailWord_6426804
  simp only [CollatzResearch.WordTrace]
  refine ⟨117202399504397096791527733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156269866005862795722036977 117202399504397096791527733)
  ·
    refine ⟨10987724953537227824205725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117202399504397096791527733 10987724953537227824205725)
    ·
      refine ⟨4120396857576460434077147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10987724953537227824205725 4120396857576460434077147)
      ·
        refine ⟨6180595286364690651115721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120396857576460434077147 6180595286364690651115721)
        ·
          refine ⟨4635446464773517988336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180595286364690651115721 4635446464773517988336791)
          ·
            refine ⟨6953169697160276982505187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635446464773517988336791 6953169697160276982505187)
            ·
              refine ⟨10429754545740415473757781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953169697160276982505187 10429754545740415473757781)
              ·
                refine ⟨122223686082895493833099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10429754545740415473757781 122223686082895493833099)
                ·
                  rfl

theorem cell23_6426804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 8].length) (baseStart_6426804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426804 prefixEnd_6426804 := by exact prefixLift 6426804
  have htrace : WordTrace (prefixWord ++ tailWord_6426804) baseStart_6426804 baseEnd_6426804 := by
    simpa [prefixWord, tailWord_6426804, baseEnd_6426804] using wordTrace_append hprefix tailTrace_6426804
  have hstable : (prefixWord ++ tailWord_6426804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426804).length < 2 ^ (prefixWord ++ tailWord_6426804).sum := by decide
  have hdescent : baseEnd_6426804 < baseStart_6426804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426816 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_6426816 : Nat := 118140960795 + 6426816 * 2 ^ 59
def prefixEnd_6426816 : Nat := 4983230072969 + 3 ^ 40 * 6426816 * 2
def baseEnd_6426816 : Nat := 3300045686006032286543617

theorem tailTrace_6426816 : CollatzResearch.WordTrace tailWord_6426816 prefixEnd_6426816 3300045686006032286543617 := by
  unfold tailWord_6426816
  simp only [CollatzResearch.WordTrace]
  refine ⟨117202618342375359816246151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156270157789833813088328201 117202618342375359816246151)
  ·
    refine ⟨175803927513563039724369227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117202618342375359816246151 175803927513563039724369227)
    ·
      refine ⟨263705891270344559586553841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175803927513563039724369227 263705891270344559586553841)
      ·
        refine ⟨197779418452758419689915381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263705891270344559586553841 197779418452758419689915381)
        ·
          refine ⟨18541820479946101845929567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197779418452758419689915381 18541820479946101845929567)
          ·
            refine ⟨27812730719919152768894351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541820479946101845929567 27812730719919152768894351)
            ·
              refine ⟨41719096079878729153341527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812730719919152768894351 41719096079878729153341527)
              ·
                refine ⟨62578644119818093730012291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41719096079878729153341527 62578644119818093730012291)
                ·
                  refine ⟨93867966179727140595018437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62578644119818093730012291 93867966179727140595018437)
                  ·
                    refine ⟨17600243658698838861565957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93867966179727140595018437 17600243658698838861565957)
                    ·
                      refine ⟨3300045686006032286543617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17600243658698838861565957 3300045686006032286543617)
                      ·
                        rfl

theorem cell23_6426816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_6426816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426816 prefixEnd_6426816 := by exact prefixLift 6426816
  have htrace : WordTrace (prefixWord ++ tailWord_6426816) baseStart_6426816 baseEnd_6426816 := by
    simpa [prefixWord, tailWord_6426816, baseEnd_6426816] using wordTrace_append hprefix tailTrace_6426816
  have hstable : (prefixWord ++ tailWord_6426816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426816).length < 2 ^ (prefixWord ++ tailWord_6426816).sum := by decide
  have hdescent : baseEnd_6426816 < baseStart_6426816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426819 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_6426819 : Nat := 118140960795 + 6426819 * 2 ^ 59
def prefixEnd_6426819 : Nat := 4983230072969 + 3 ^ 40 * 6426819 * 2
def baseEnd_6426819 : Nat := 3300047226447995774806103

theorem tailTrace_6426819 : CollatzResearch.WordTrace tailWord_6426819 prefixEnd_6426819 3300047226447995774806103 := by
  unfold tailWord_6426819
  simp only [CollatzResearch.WordTrace]
  refine ⟨234405346103739851144851511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156270230735826567429901007 234405346103739851144851511)
  ·
    refine ⟨351608019155609776717277267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234405346103739851144851511 351608019155609776717277267)
    ·
      refine ⟨527412028733414665075915901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351608019155609776717277267 527412028733414665075915901)
      ·
        refine ⟨197779510775030499403468463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527412028733414665075915901 197779510775030499403468463)
        ·
          refine ⟨296669266162545749105202695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197779510775030499403468463 296669266162545749105202695)
          ·
            refine ⟨445003899243818623657804043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296669266162545749105202695 445003899243818623657804043)
            ·
              refine ⟨667505848865727935486706065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445003899243818623657804043 667505848865727935486706065)
              ·
                refine ⟨500629386649295951615029549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667505848865727935486706065 500629386649295951615029549)
                ·
                  refine ⟨187736019993485981855636081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500629386649295951615029549 187736019993485981855636081)
                  ·
                    refine ⟨140802014995114486391727061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187736019993485981855636081 140802014995114486391727061)
                    ·
                      refine ⟨3300047226447995774806103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140802014995114486391727061 3300047226447995774806103)
                      ·
                        rfl

theorem cell23_6426819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_6426819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426819 prefixEnd_6426819 := by exact prefixLift 6426819
  have htrace : WordTrace (prefixWord ++ tailWord_6426819) baseStart_6426819 baseEnd_6426819 := by
    simpa [prefixWord, tailWord_6426819, baseEnd_6426819] using wordTrace_append hprefix tailTrace_6426819
  have hstable : (prefixWord ++ tailWord_6426819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426819).length < 2 ^ (prefixWord ++ tailWord_6426819).sum := by decide
  have hdescent : baseEnd_6426819 < baseStart_6426819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426820 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_6426820 : Nat := 118140960795 + 6426820 * 2 ^ 59
def prefixEnd_6426820 : Nat := 4983230072969 + 3 ^ 40 * 6426820 * 2
def baseEnd_6426820 : Nat := 3300047739928650270893599

theorem tailTrace_6426820 : CollatzResearch.WordTrace tailWord_6426820 prefixEnd_6426820 3300047739928650270893599 := by
  unfold tailWord_6426820
  simp only [CollatzResearch.WordTrace]
  refine ⟨117202691288368114157818957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156270255051157485543758609 117202691288368114157818957)
  ·
    refine ⟨43951009233138042809182109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117202691288368114157818957 43951009233138042809182109)
    ·
      refine ⟨16481628462426766053443291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43951009233138042809182109 16481628462426766053443291)
      ·
        refine ⟨24722442693640149080164937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16481628462426766053443291 24722442693640149080164937)
        ·
          refine ⟨18541832020230111810123703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24722442693640149080164937 18541832020230111810123703)
          ·
            refine ⟨27812748030345167715185555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541832020230111810123703 27812748030345167715185555)
            ·
              refine ⟨41719122045517751572778333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812748030345167715185555 41719122045517751572778333)
              ·
                refine ⟨15644670767069156839791875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41719122045517751572778333 15644670767069156839791875)
                ·
                  refine ⟨23467006150603735259687813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644670767069156839791875 23467006150603735259687813)
                  ·
                    refine ⟨4400063653238200361191465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23467006150603735259687813 4400063653238200361191465)
                    ·
                      refine ⟨3300047739928650270893599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400063653238200361191465 3300047739928650270893599)
                      ·
                        rfl

theorem cell23_6426820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_6426820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426820 prefixEnd_6426820 := by exact prefixLift 6426820
  have htrace : WordTrace (prefixWord ++ tailWord_6426820) baseStart_6426820 baseEnd_6426820 := by
    simpa [prefixWord, tailWord_6426820, baseEnd_6426820] using wordTrace_append hprefix tailTrace_6426820
  have hstable : (prefixWord ++ tailWord_6426820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426820).length < 2 ^ (prefixWord ++ tailWord_6426820).sum := by decide
  have hdescent : baseEnd_6426820 < baseStart_6426820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426826 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_6426826 : Nat := 118140960795 + 6426826 * 2 ^ 59
def prefixEnd_6426826 : Nat := 4983230072969 + 3 ^ 40 * 6426826 * 2
def baseEnd_6426826 : Nat := 366672313423619694157619

theorem tailTrace_6426826 : CollatzResearch.WordTrace tailWord_6426826 prefixEnd_6426826 366672313423619694157619 := by
  unfold tailWord_6426826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58601400353678622835089083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156270400943142994226904221 58601400353678622835089083)
  ·
    refine ⟨87902100530517934252633625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58601400353678622835089083 87902100530517934252633625)
    ·
      refine ⟨65926575397888450689475219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87902100530517934252633625 65926575397888450689475219)
      ·
        refine ⟨98889863096832676034212829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65926575397888450689475219 98889863096832676034212829)
        ·
          refine ⟨37083698661312253512829811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98889863096832676034212829 37083698661312253512829811)
          ·
            refine ⟨55625547991968380269244717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37083698661312253512829811 55625547991968380269244717)
            ·
              refine ⟨20859580496988142600966769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55625547991968380269244717 20859580496988142600966769)
              ·
                refine ⟨15644685372741106950725077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20859580496988142600966769 15644685372741106950725077)
                ·
                  refine ⟨366672313423619694157619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15644685372741106950725077 366672313423619694157619)
                  ·
                    rfl

theorem cell23_6426826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_6426826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426826 prefixEnd_6426826 := by exact prefixLift 6426826
  have htrace : WordTrace (prefixWord ++ tailWord_6426826) baseStart_6426826 baseEnd_6426826 := by
    simpa [prefixWord, tailWord_6426826, baseEnd_6426826] using wordTrace_append hprefix tailTrace_6426826
  have hstable : (prefixWord ++ tailWord_6426826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426826).length < 2 ^ (prefixWord ++ tailWord_6426826).sum := by decide
  have hdescent : baseEnd_6426826 < baseStart_6426826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426853 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6426853 : Nat := 118140960795 + 6426853 * 2 ^ 59
def prefixEnd_6426853 : Nat := 4983230072969 + 3 ^ 40 * 6426853 * 2
def baseEnd_6426853 : Nat := 3300064684790248641780947

theorem tailTrace_6426853 : CollatzResearch.WordTrace tailWord_6426853 prefixEnd_6426853 3300064684790248641780947 := by
  unfold tailWord_6426853
  simp only [CollatzResearch.WordTrace]
  refine ⟨234406586185616674951589213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156271057457077783301059475 234406586185616674951589213)
  ·
    refine ⟨87902469819606253106845955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234406586185616674951589213 87902469819606253106845955)
    ·
      refine ⟨131853704729409379660268933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87902469819606253106845955 131853704729409379660268933)
      ·
        refine ⟨24722569636764258686300425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131853704729409379660268933 24722569636764258686300425)
        ·
          refine ⟨18541927227573194014725319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24722569636764258686300425 18541927227573194014725319)
          ·
            refine ⟨27812890841359791022087979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541927227573194014725319 27812890841359791022087979)
            ·
              refine ⟨41719336262039686533131969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812890841359791022087979 41719336262039686533131969)
              ·
                refine ⟨31289502196529764899848977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41719336262039686533131969 31289502196529764899848977)
                ·
                  refine ⟨23467126647397323674886733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31289502196529764899848977 23467126647397323674886733)
                  ·
                    refine ⟨8800172492773996378082525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23467126647397323674886733 8800172492773996378082525)
                    ·
                      refine ⟨3300064684790248641780947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800172492773996378082525 3300064684790248641780947)
                      ·
                        rfl

theorem cell23_6426853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6426853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426853 prefixEnd_6426853 := by exact prefixLift 6426853
  have htrace : WordTrace (prefixWord ++ tailWord_6426853) baseStart_6426853 baseEnd_6426853 := by
    simpa [prefixWord, tailWord_6426853, baseEnd_6426853] using wordTrace_append hprefix tailTrace_6426853
  have hstable : (prefixWord ++ tailWord_6426853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426853).length < 2 ^ (prefixWord ++ tailWord_6426853).sum := by decide
  have hdescent : baseEnd_6426853 < baseStart_6426853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426913 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6426913 : Nat := 118140960795 + 6426913 * 2 ^ 59
def prefixEnd_6426913 : Nat := 4983230072969 + 3 ^ 40 * 6426913 * 2
def baseEnd_6426913 : Nat := 3300095493629518407030671

theorem tailTrace_6426913 : CollatzResearch.WordTrace tailWord_6426913 prefixEnd_6426913 3300095493629518407030671 := by
  unfold tailWord_6426913
  simp only [CollatzResearch.WordTrace]
  refine ⟨234408774565399305198773393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156272516376932870132515595 234408774565399305198773393)
  ·
    refine ⟨175806580924049478899080045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234408774565399305198773393 175806580924049478899080045)
    ·
      refine ⟨65927467846518554587155017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175806580924049478899080045 65927467846518554587155017)
      ·
        refine ⟨49445600884888915940366263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65927467846518554587155017 49445600884888915940366263)
        ·
          refine ⟨74168401327333373910549395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49445600884888915940366263 74168401327333373910549395)
          ·
            refine ⟨111252601991000060865824093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74168401327333373910549395 111252601991000060865824093)
            ·
              refine ⟨41719725746625022824684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111252601991000060865824093 41719725746625022824684035)
              ·
                refine ⟨62579588619937534237026053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41719725746625022824684035 62579588619937534237026053)
                ·
                  refine ⟨11733672866238287669442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62579588619937534237026053 11733672866238287669442385)
                  ·
                    refine ⟨8800254649678715752081789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11733672866238287669442385 8800254649678715752081789)
                    ·
                      refine ⟨3300095493629518407030671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800254649678715752081789 3300095493629518407030671)
                      ·
                        rfl

theorem cell23_6426913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6426913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426913 prefixEnd_6426913 := by exact prefixLift 6426913
  have htrace : WordTrace (prefixWord ++ tailWord_6426913) baseStart_6426913 baseEnd_6426913 := by
    simpa [prefixWord, tailWord_6426913, baseEnd_6426913] using wordTrace_append hprefix tailTrace_6426913
  have hstable : (prefixWord ++ tailWord_6426913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426913).length < 2 ^ (prefixWord ++ tailWord_6426913).sum := by decide
  have hdescent : baseEnd_6426913 < baseStart_6426913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426933 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 6]
def baseStart_6426933 : Nat := 118140960795 + 6426933 * 2 ^ 59
def prefixEnd_6426933 : Nat := 4983230072969 + 3 ^ 40 * 6426933 * 2
def baseEnd_6426933 : Nat := 366678418138067592086731

theorem tailTrace_6426933 : CollatzResearch.WordTrace tailWord_6426933 prefixEnd_6426933 366678418138067592086731 := by
  unfold tailWord_6426933
  simp only [CollatzResearch.WordTrace]
  refine ⟨234409504025326848614501453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156273002683551232409667635 234409504025326848614501453)
  ·
    refine ⟨87903564009497568230438045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234409504025326848614501453 87903564009497568230438045)
    ·
      refine ⟨32963836503561588086414267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87903564009497568230438045 32963836503561588086414267)
      ·
        refine ⟨49445754755342382129621401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32963836503561588086414267 49445754755342382129621401)
        ·
          refine ⟨37084316066506786597216051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49445754755342382129621401 37084316066506786597216051)
          ·
            refine ⟨55626474099760179895824077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37084316066506786597216051 55626474099760179895824077)
            ·
              refine ⟨20859927787410067460934029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55626474099760179895824077 20859927787410067460934029)
              ·
                refine ⟨7822472920278775297850261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20859927787410067460934029 7822472920278775297850261)
                ·
                  refine ⟨366678418138067592086731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7822472920278775297850261 366678418138067592086731)
                  ·
                    rfl

theorem cell23_6426933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_6426933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426933 prefixEnd_6426933 := by exact prefixLift 6426933
  have htrace : WordTrace (prefixWord ++ tailWord_6426933) baseStart_6426933 baseEnd_6426933 := by
    simpa [prefixWord, tailWord_6426933, baseEnd_6426933] using wordTrace_append hprefix tailTrace_6426933
  have hstable : (prefixWord ++ tailWord_6426933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426933).length < 2 ^ (prefixWord ++ tailWord_6426933).sum := by decide
  have hdescent : baseEnd_6426933 < baseStart_6426933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426936 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_6426936 : Nat := 118140960795 + 6426936 * 2 ^ 59
def prefixEnd_6426936 : Nat := 4983230072969 + 3 ^ 40 * 6426936 * 2
def baseEnd_6426936 : Nat := 3300107303684571817043065

theorem tailTrace_6426936 : CollatzResearch.WordTrace tailWord_6426936 prefixEnd_6426936 3300107303684571817043065 := by
  unfold tailWord_6426936
  simp only [CollatzResearch.WordTrace]
  refine ⟨117204806722157990063430331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156273075629543986751240441 117204806722157990063430331)
  ·
    refine ⟨175807210083236985095145497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117204806722157990063430331 175807210083236985095145497)
    ·
      refine ⟨131855407562427738821359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175807210083236985095145497 131855407562427738821359123)
      ·
        refine ⟨197783111343641608232038685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131855407562427738821359123 197783111343641608232038685)
        ·
          refine ⟨74168666753865603087014507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197783111343641608232038685 74168666753865603087014507)
          ·
            refine ⟨111253000130798404630521761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74168666753865603087014507 111253000130798404630521761)
            ·
              refine ⟨83439750098098803472891321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111253000130798404630521761 83439750098098803472891321)
              ·
                refine ⟨62579812573574102604668491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83439750098098803472891321 62579812573574102604668491)
                ·
                  refine ⟨93869718860361153907002737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62579812573574102604668491 93869718860361153907002737)
                  ·
                    refine ⟨70402289145270865430252053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93869718860361153907002737 70402289145270865430252053)
                    ·
                      refine ⟨3300107303684571817043065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70402289145270865430252053 3300107303684571817043065)
                      ·
                        rfl

theorem cell23_6426936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_6426936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426936 prefixEnd_6426936 := by exact prefixLift 6426936
  have htrace : WordTrace (prefixWord ++ tailWord_6426936) baseStart_6426936 baseEnd_6426936 := by
    simpa [prefixWord, tailWord_6426936, baseEnd_6426936] using wordTrace_append hprefix tailTrace_6426936
  have hstable : (prefixWord ++ tailWord_6426936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426936).length < 2 ^ (prefixWord ++ tailWord_6426936).sum := by decide
  have hdescent : baseEnd_6426936 < baseStart_6426936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426993 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_6426993 : Nat := 118140960795 + 6426993 * 2 ^ 59
def prefixEnd_6426993 : Nat := 4983230072969 + 3 ^ 40 * 6426993 * 2
def baseEnd_6426993 : Nat := 1100045524027292698010101

theorem tailTrace_6426993 : CollatzResearch.WordTrace tailWord_6426993 prefixEnd_6426993 1100045524027292698010101 := by
  unfold tailWord_6426993
  simp only [CollatzResearch.WordTrace]
  refine ⟨234411692405109478861685633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156274461603406319241123755 234411692405109478861685633)
  ·
    refine ⟨175808769303832109146264225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234411692405109478861685633 175808769303832109146264225)
    ·
      refine ⟨131856576977874081859698169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175808769303832109146264225 131856576977874081859698169)
      ·
        refine ⟨98892432733405561394773627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131856576977874081859698169 98892432733405561394773627)
        ·
          refine ⟨148338649100108342092160441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98892432733405561394773627 148338649100108342092160441)
          ·
            refine ⟨111253986825081256569120331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148338649100108342092160441 111253986825081256569120331)
            ·
              refine ⟨166880980237621884853680497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111253986825081256569120331 166880980237621884853680497)
              ·
                refine ⟨125160735178216413640260373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166880980237621884853680497 125160735178216413640260373)
                ·
                  refine ⟨5866909461478894389387205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125160735178216413640260373 5866909461478894389387205)
                  ·
                    refine ⟨1100045524027292698010101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5866909461478894389387205 1100045524027292698010101)
                    ·
                      rfl

theorem cell23_6426993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_6426993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6426993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6426993 prefixEnd_6426993 := by exact prefixLift 6426993
  have htrace : WordTrace (prefixWord ++ tailWord_6426993) baseStart_6426993 baseEnd_6426993 := by
    simpa [prefixWord, tailWord_6426993, baseEnd_6426993] using wordTrace_append hprefix tailTrace_6426993
  have hstable : (prefixWord ++ tailWord_6426993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426993).length < 2 ^ (prefixWord ++ tailWord_6426993).sum := by decide
  have hdescent : baseEnd_6426993 < baseStart_6426993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427017 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 1, 1, 4]
def baseStart_6427017 : Nat := 118140960795 + 6427017 * 2 ^ 59
def prefixEnd_6427017 : Nat := 4983230072969 + 3 ^ 40 * 6427017 * 2
def baseEnd_6427017 : Nat := 3300148895617586000130193

theorem tailTrace_6427017 : CollatzResearch.WordTrace tailWord_6427017 prefixEnd_6427017 3300148895617586000130193 := by
  unfold tailWord_6427017
  simp only [CollatzResearch.WordTrace]
  refine ⟨234412567757022530960559305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156275045171348353973706203 234412567757022530960559305)
  ·
    refine ⟨175809425817766898220419479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234412567757022530960559305 175809425817766898220419479)
    ·
      refine ⟨263714138726650347330629219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175809425817766898220419479 263714138726650347330629219)
      ·
        refine ⟨395571208089975520995943829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263714138726650347330629219 395571208089975520995943829)
        ·
          refine ⟨18542400379217602546684867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 395571208089975520995943829 18542400379217602546684867)
          ·
            refine ⟨27813600568826403820027301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18542400379217602546684867 27813600568826403820027301)
            ·
              refine ⟨5215050106654950716255119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27813600568826403820027301 5215050106654950716255119)
              ·
                refine ⟨7822575159982426074382679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215050106654950716255119 7822575159982426074382679)
                ·
                  refine ⟨11733862739973639111574019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7822575159982426074382679 11733862739973639111574019)
                  ·
                    refine ⟨17600794109960458667361029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11733862739973639111574019 17600794109960458667361029)
                    ·
                      refine ⟨3300148895617586000130193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17600794109960458667361029 3300148895617586000130193)
                      ·
                        rfl

theorem cell23_6427017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 1, 4].length) (baseStart_6427017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427017 prefixEnd_6427017 := by exact prefixLift 6427017
  have htrace : WordTrace (prefixWord ++ tailWord_6427017) baseStart_6427017 baseEnd_6427017 := by
    simpa [prefixWord, tailWord_6427017, baseEnd_6427017] using wordTrace_append hprefix tailTrace_6427017
  have hstable : (prefixWord ++ tailWord_6427017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427017).length < 2 ^ (prefixWord ++ tailWord_6427017).sum := by decide
  have hdescent : baseEnd_6427017 < baseStart_6427017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427034 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6427034 : Nat := 118140960795 + 6427034 * 2 ^ 59
def prefixEnd_6427034 : Nat := 4983230072969 + 3 ^ 40 * 6427034 * 2
def baseEnd_6427034 : Nat := 3300157624788712433617615

theorem tailTrace_6427034 : CollatzResearch.WordTrace tailWord_6427034 prefixEnd_6427034 3300157624788712433617615 := by
  unfold tailWord_6427034
  simp only [CollatzResearch.WordTrace]
  refine ⟨58603296949490235715982039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156275458531973961909285437 58603296949490235715982039)
  ·
    refine ⟨87904945424235353573973059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58603296949490235715982039 87904945424235353573973059)
    ·
      refine ⟨131857418136353030360959589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87904945424235353573973059 131857418136353030360959589)
      ·
        refine ⟨24723265900566193192679923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131857418136353030360959589 24723265900566193192679923)
        ·
          refine ⟨37084898850849289789019885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24723265900566193192679923 37084898850849289789019885)
          ·
            refine ⟨13906837069068483670882457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37084898850849289789019885 13906837069068483670882457)
            ·
              refine ⟨10430127801801362753161843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13906837069068483670882457 10430127801801362753161843)
              ·
                refine ⟨15645191702702044129742765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430127801801362753161843 15645191702702044129742765)
                ·
                  refine ⟨5866946888513266548653537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15645191702702044129742765 5866946888513266548653537)
                  ·
                    refine ⟨4400210166384949911490153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5866946888513266548653537 4400210166384949911490153)
                    ·
                      refine ⟨3300157624788712433617615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400210166384949911490153 3300157624788712433617615)
                      ·
                        rfl

theorem cell23_6427034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6427034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427034 prefixEnd_6427034 := by exact prefixLift 6427034
  have htrace : WordTrace (prefixWord ++ tailWord_6427034) baseStart_6427034 baseEnd_6427034 := by
    simpa [prefixWord, tailWord_6427034, baseEnd_6427034] using wordTrace_append hprefix tailTrace_6427034
  have hstable : (prefixWord ++ tailWord_6427034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427034).length < 2 ^ (prefixWord ++ tailWord_6427034).sum := by decide
  have hdescent : baseEnd_6427034 < baseStart_6427034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427047 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6427047 : Nat := 118140960795 + 6427047 * 2 ^ 59
def prefixEnd_6427047 : Nat := 4983230072969 + 3 ^ 40 * 6427047 * 2
def baseEnd_6427047 : Nat := 3300164300037220882755055

theorem tailTrace_6427047 : CollatzResearch.WordTrace tailWord_6427047 prefixEnd_6427047 3300164300037220882755055 := by
  unfold tailWord_6427047
  simp only [CollatzResearch.WordTrace]
  refine ⟨234413661946913846084151395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156275774631275897389434263 234413661946913846084151395)
  ·
    refine ⟨351620492920370769126227093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234413661946913846084151395 351620492920370769126227093)
    ·
      refine ⟨16482210605642379802791895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 351620492920370769126227093 16482210605642379802791895)
      ·
        refine ⟨24723315908463569704187843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16482210605642379802791895 24723315908463569704187843)
        ·
          refine ⟨37084973862695354556281765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24723315908463569704187843 37084973862695354556281765)
          ·
            refine ⟨6953432599255378979302831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37084973862695354556281765 6953432599255378979302831)
            ·
              refine ⟨10430148898883068468954247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953432599255378979302831 10430148898883068468954247)
              ·
                refine ⟨15645223348324602703431371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430148898883068468954247 15645223348324602703431371)
                ·
                  refine ⟨23467835022486904055147057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15645223348324602703431371 23467835022486904055147057)
                  ·
                    refine ⟨17600876266865178041360293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23467835022486904055147057 17600876266865178041360293)
                    ·
                      refine ⟨3300164300037220882755055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17600876266865178041360293 3300164300037220882755055)
                      ·
                        rfl

theorem cell23_6427047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6427047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427047 prefixEnd_6427047 := by exact prefixLift 6427047
  have htrace : WordTrace (prefixWord ++ tailWord_6427047) baseStart_6427047 baseEnd_6427047 := by
    simpa [prefixWord, tailWord_6427047, baseEnd_6427047] using wordTrace_append hprefix tailTrace_6427047
  have hstable : (prefixWord ++ tailWord_6427047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427047).length < 2 ^ (prefixWord ++ tailWord_6427047).sum := by decide
  have hdescent : baseEnd_6427047 < baseStart_6427047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427063 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_6427063 : Nat := 118140960795 + 6427063 * 2 ^ 59
def prefixEnd_6427063 : Nat := 4983230072969 + 3 ^ 40 * 6427063 * 2
def baseEnd_6427063 : Nat := 3300172515727692820154981

theorem tailTrace_6427063 : CollatzResearch.WordTrace tailWord_6427063 prefixEnd_6427063 3300172515727692820154981 := by
  unfold tailWord_6427063
  simp only [CollatzResearch.WordTrace]
  refine ⟨234414245514855880816733843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156276163676570587211155895 234414245514855880816733843)
  ·
    refine ⟨351621368272283821225100765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234414245514855880816733843 351621368272283821225100765)
    ·
      refine ⟨131858013102106432959412787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351621368272283821225100765 131858013102106432959412787)
      ·
        refine ⟨197787019653159649439119181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131858013102106432959412787 197787019653159649439119181)
        ·
          refine ⟨74170132369934868539669693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197787019653159649439119181 74170132369934868539669693)
          ·
            refine ⟨27813799638725575702376135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74170132369934868539669693 27813799638725575702376135)
            ·
              refine ⟨41720699458088363553564203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27813799638725575702376135 41720699458088363553564203)
              ·
                refine ⟨62581049187132545330346305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41720699458088363553564203 62581049187132545330346305)
                ·
                  refine ⟨46935786890349408997759729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62581049187132545330346305 46935786890349408997759729)
                  ·
                    refine ⟨35201840167762056748319797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46935786890349408997759729 35201840167762056748319797)
                    ·
                      refine ⟨3300172515727692820154981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35201840167762056748319797 3300172515727692820154981)
                      ·
                        rfl

theorem cell23_6427063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_6427063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427063 prefixEnd_6427063 := by exact prefixLift 6427063
  have htrace : WordTrace (prefixWord ++ tailWord_6427063) baseStart_6427063 baseEnd_6427063 := by
    simpa [prefixWord, tailWord_6427063, baseEnd_6427063] using wordTrace_append hprefix tailTrace_6427063
  have hstable : (prefixWord ++ tailWord_6427063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427063).length < 2 ^ (prefixWord ++ tailWord_6427063).sum := by decide
  have hdescent : baseEnd_6427063 < baseStart_6427063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427068 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6427068 : Nat := 118140960795 + 6427068 * 2 ^ 59
def prefixEnd_6427068 : Nat := 4983230072969 + 3 ^ 40 * 6427068 * 2
def baseEnd_6427068 : Nat := 3300175083130965300592459

theorem tailTrace_6427068 : CollatzResearch.WordTrace tailWord_6427068 prefixEnd_6427068 3300175083130965300592459 := by
  unfold tailWord_6427068
  simp only [CollatzResearch.WordTrace]
  refine ⟨117207213939918883335332929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156276285253225177780443905 117207213939918883335332929)
  ·
    refine ⟨87905410454939162501499697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117207213939918883335332929 87905410454939162501499697)
    ·
      refine ⟨65929057841204371876124773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87905410454939162501499697 65929057841204371876124773)
      ·
        refine ⟨12361698345225819726773395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65929057841204371876124773 12361698345225819726773395)
        ·
          refine ⟨18542547517838729590160093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12361698345225819726773395 18542547517838729590160093)
          ·
            refine ⟨6953455319189523596310035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18542547517838729590160093 6953455319189523596310035)
            ·
              refine ⟨10430182978784285394465053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953455319189523596310035 10430182978784285394465053)
              ·
                refine ⟨3911318617044107022924395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10430182978784285394465053 3911318617044107022924395)
                ·
                  refine ⟨5866977925566160534386593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911318617044107022924395 5866977925566160534386593)
                  ·
                    refine ⟨4400233444174620400789945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5866977925566160534386593 4400233444174620400789945)
                    ·
                      refine ⟨3300175083130965300592459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400233444174620400789945 3300175083130965300592459)
                      ·
                        rfl

theorem cell23_6427068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6427068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427068 prefixEnd_6427068 := by exact prefixLift 6427068
  have htrace : WordTrace (prefixWord ++ tailWord_6427068) baseStart_6427068 baseEnd_6427068 := by
    simpa [prefixWord, tailWord_6427068, baseEnd_6427068] using wordTrace_append hprefix tailTrace_6427068
  have hstable : (prefixWord ++ tailWord_6427068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427068).length < 2 ^ (prefixWord ++ tailWord_6427068).sum := by decide
  have hdescent : baseEnd_6427068 < baseStart_6427068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427094 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6427094 : Nat := 118140960795 + 6427094 * 2 ^ 59
def prefixEnd_6427094 : Nat := 4983230072969 + 3 ^ 40 * 6427094 * 2
def baseEnd_6427094 : Nat := 3300188433627982198867339

theorem tailTrace_6427094 : CollatzResearch.WordTrace tailWord_6427094 prefixEnd_6427094 3300188433627982198867339 := by
  unfold tailWord_6427094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650961011108973319444521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156276917451829048740741557 14650961011108973319444521)
  ·
    refine ⟨10988220758331729989583391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14650961011108973319444521 10988220758331729989583391)
    ·
      refine ⟨16482331137497594984375087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988220758331729989583391 16482331137497594984375087)
      ·
        refine ⟨24723496706246392476562631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16482331137497594984375087 24723496706246392476562631)
        ·
          refine ⟨37085245059369588714843947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24723496706246392476562631 37085245059369588714843947)
          ·
            refine ⟨55627867589054383072265921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37085245059369588714843947 55627867589054383072265921)
            ·
              refine ⟨41720900691790787304199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55627867589054383072265921 41720900691790787304199441)
              ·
                refine ⟨31290675518843090478149581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41720900691790787304199441 31290675518843090478149581)
                ·
                  refine ⟨11734003319566158929306093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31290675518843090478149581 11734003319566158929306093)
                  ·
                    refine ⟨4400251244837309598489785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11734003319566158929306093 4400251244837309598489785)
                    ·
                      refine ⟨3300188433627982198867339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400251244837309598489785 3300188433627982198867339)
                      ·
                        rfl

theorem cell23_6427094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6427094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427094 prefixEnd_6427094 := by exact prefixLift 6427094
  have htrace : WordTrace (prefixWord ++ tailWord_6427094) baseStart_6427094 baseEnd_6427094 := by
    simpa [prefixWord, tailWord_6427094, baseEnd_6427094] using wordTrace_append hprefix tailTrace_6427094
  have hstable : (prefixWord ++ tailWord_6427094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427094).length < 2 ^ (prefixWord ++ tailWord_6427094).sum := by decide
  have hdescent : baseEnd_6427094 < baseStart_6427094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427147 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 5]
def baseStart_6427147 : Nat := 118140960795 + 6427147 * 2 ^ 59
def prefixEnd_6427147 : Nat := 4983230072969 + 3 ^ 40 * 6427147 * 2
def baseEnd_6427147 : Nat := 366690627566963387944955

theorem tailTrace_6427147 : CollatzResearch.WordTrace tailWord_6427147 prefixEnd_6427147 366690627566963387944955 := by
  unfold tailWord_6427147
  simp only [CollatzResearch.WordTrace]
  refine ⟨234417309246551563162791695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156278206164367708775194463 234417309246551563162791695)
  ·
    refine ⟨351625963869827344744187543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234417309246551563162791695 351625963869827344744187543)
    ·
      refine ⟨527438945804741017116281315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351625963869827344744187543 527438945804741017116281315)
      ·
        refine ⟨791158418707111525674421973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527438945804741017116281315 791158418707111525674421973)
        ·
          refine ⟨18542775438447926382994265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 791158418707111525674421973 18542775438447926382994265)
          ·
            refine ⟨13907081578835944787245699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18542775438447926382994265 13907081578835944787245699)
            ·
              refine ⟨20860622368253917180868549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907081578835944787245699 20860622368253917180868549)
              ·
                refine ⟨3911366694047609471412853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20860622368253917180868549 3911366694047609471412853)
                ·
                  refine ⟨366690627566963387944955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3911366694047609471412853 366690627566963387944955)
                  ·
                    rfl

theorem cell23_6427147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 5].length) (baseStart_6427147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427147 prefixEnd_6427147 := by exact prefixLift 6427147
  have htrace : WordTrace (prefixWord ++ tailWord_6427147) baseStart_6427147 baseEnd_6427147 := by
    simpa [prefixWord, tailWord_6427147, baseEnd_6427147] using wordTrace_append hprefix tailTrace_6427147
  have hstable : (prefixWord ++ tailWord_6427147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427147).length < 2 ^ (prefixWord ++ tailWord_6427147).sum := by decide
  have hdescent : baseEnd_6427147 < baseStart_6427147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427153 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_6427153 : Nat := 118140960795 + 6427153 * 2 ^ 59
def prefixEnd_6427153 : Nat := 4983230072969 + 3 ^ 40 * 6427153 * 2
def baseEnd_6427153 : Nat := 3300218728986597468029567

theorem tailTrace_6427153 : CollatzResearch.WordTrace tailWord_6427153 prefixEnd_6427153 3300218728986597468029567 := by
  unfold tailWord_6427153
  simp only [CollatzResearch.WordTrace]
  refine ⟨234417528084529826187510113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156278352056353217458340075 234417528084529826187510113)
  ·
    refine ⟨175813146063397369640632585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234417528084529826187510113 175813146063397369640632585)
    ·
      refine ⟨131859859547548027230474439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175813146063397369640632585 131859859547548027230474439)
      ·
        refine ⟨197789789321322040845711659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131859859547548027230474439 197789789321322040845711659)
        ·
          refine ⟨296684683981983061268567489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197789789321322040845711659 296684683981983061268567489)
          ·
            refine ⟨222513512986487295951425617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296684683981983061268567489 222513512986487295951425617)
            ·
              refine ⟨166885134739865471963569213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222513512986487295951425617 166885134739865471963569213)
              ·
                refine ⟨62581925527449551986338455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166885134739865471963569213 62581925527449551986338455)
                ·
                  refine ⟨93872888291174327979507683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62581925527449551986338455 93872888291174327979507683)
                  ·
                    refine ⟨140809332436761491969261525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93872888291174327979507683 140809332436761491969261525)
                    ·
                      refine ⟨3300218728986597468029567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140809332436761491969261525 3300218728986597468029567)
                      ·
                        rfl

theorem cell23_6427153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_6427153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427153 prefixEnd_6427153 := by exact prefixLift 6427153
  have htrace : WordTrace (prefixWord ++ tailWord_6427153) baseStart_6427153 baseEnd_6427153 := by
    simpa [prefixWord, tailWord_6427153, baseEnd_6427153] using wordTrace_append hprefix tailTrace_6427153
  have hstable : (prefixWord ++ tailWord_6427153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427153).length < 2 ^ (prefixWord ++ tailWord_6427153).sum := by decide
  have hdescent : baseEnd_6427153 < baseStart_6427153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427207 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 3, 4]
def baseStart_6427207 : Nat := 118140960795 + 6427207 * 2 ^ 59
def prefixEnd_6427207 : Nat := 4983230072969 + 3 ^ 40 * 6427207 * 2
def baseEnd_6427207 : Nat := 1100082152313980085584773

theorem tailTrace_6427207 : CollatzResearch.WordTrace tailWord_6427207 prefixEnd_6427207 1100082152313980085584773 := by
  unfold tailWord_6427207
  simp only [CollatzResearch.WordTrace]
  refine ⟨234419497626334193409975875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156279665084222795606650583 234419497626334193409975875)
  ·
    refine ⟨351629246439501290114963813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234419497626334193409975875 351629246439501290114963813)
    ·
      refine ⟨65930483707406491896555715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351629246439501290114963813 65930483707406491896555715)
      ·
        refine ⟨98895725561109737844833573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65930483707406491896555715 98895725561109737844833573)
        ·
          refine ⟨18542948542708075845906295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98895725561109737844833573 18542948542708075845906295)
          ·
            refine ⟨27814422814062113768859443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18542948542708075845906295 27814422814062113768859443)
            ·
              refine ⟨41721634221093170653289165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27814422814062113768859443 41721634221093170653289165)
              ·
                refine ⟨15645612832909938994983437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41721634221093170653289165 15645612832909938994983437)
                ·
                  refine ⟨5867104812341227123118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15645612832909938994983437 5867104812341227123118789)
                  ·
                    refine ⟨1100082152313980085584773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5867104812341227123118789 1100082152313980085584773)
                    ·
                      rfl

theorem cell23_6427207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_6427207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427207 prefixEnd_6427207 := by exact prefixLift 6427207
  have htrace : WordTrace (prefixWord ++ tailWord_6427207) baseStart_6427207 baseEnd_6427207 := by
    simpa [prefixWord, tailWord_6427207, baseEnd_6427207] using wordTrace_append hprefix tailTrace_6427207
  have hstable : (prefixWord ++ tailWord_6427207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427207).length < 2 ^ (prefixWord ++ tailWord_6427207).sum := by decide
  have hdescent : baseEnd_6427207 < baseStart_6427207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427247 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_6427247 : Nat := 118140960795 + 6427247 * 2 ^ 59
def prefixEnd_6427247 : Nat := 4983230072969 + 3 ^ 40 * 6427247 * 2
def baseEnd_6427247 : Nat := 3300266996168120100254135

theorem tailTrace_6427247 : CollatzResearch.WordTrace tailWord_6427247 prefixEnd_6427247 3300266996168120100254135 := by
  unfold tailWord_6427247
  simp only [CollatzResearch.WordTrace]
  refine ⟨234420956546189280241431995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156280637697459520160954663 234420956546189280241431995)
  ·
    refine ⟨351631434819283920362147993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234420956546189280241431995 351631434819283920362147993)
    ·
      refine ⟨263723576114462940271610995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351631434819283920362147993 263723576114462940271610995)
      ·
        refine ⟨395585364171694410407416493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263723576114462940271610995 395585364171694410407416493)
        ·
          refine ⟨148344511564385403902781185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395585364171694410407416493 148344511564385403902781185)
          ·
            refine ⟨111258383673289052927085889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148344511564385403902781185 111258383673289052927085889)
            ·
              refine ⟨83443787754966789695314417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111258383673289052927085889 83443787754966789695314417)
              ·
                refine ⟨62582840816225092271485813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83443787754966789695314417 62582840816225092271485813)
                ·
                  refine ⟨5867141326521102400451795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62582840816225092271485813 5867141326521102400451795)
                  ·
                    refine ⟨8800711989781653600677693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867141326521102400451795 8800711989781653600677693)
                    ·
                      refine ⟨3300266996168120100254135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800711989781653600677693 3300266996168120100254135)
                      ·
                        rfl

theorem cell23_6427247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_6427247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427247 prefixEnd_6427247 := by exact prefixLift 6427247
  have htrace : WordTrace (prefixWord ++ tailWord_6427247) baseStart_6427247 baseEnd_6427247 := by
    simpa [prefixWord, tailWord_6427247, baseEnd_6427247] using wordTrace_append hprefix tailTrace_6427247
  have hstable : (prefixWord ++ tailWord_6427247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427247).length < 2 ^ (prefixWord ++ tailWord_6427247).sum := by decide
  have hdescent : baseEnd_6427247 < baseStart_6427247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427264 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_6427264 : Nat := 118140960795 + 6427264 * 2 ^ 59
def prefixEnd_6427264 : Nat := 4983230072969 + 3 ^ 40 * 6427264 * 2
def baseEnd_6427264 : Nat := 3300275725339246533741557

theorem tailTrace_6427264 : CollatzResearch.WordTrace tailWord_6427264 prefixEnd_6427264 3300275725339246533741557 := by
  unfold tailWord_6427264
  simp only [CollatzResearch.WordTrace]
  refine ⟨117210788293563846072400423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156281051058085128096533897 117210788293563846072400423)
  ·
    refine ⟨175816182440345769108600635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117210788293563846072400423 175816182440345769108600635)
    ·
      refine ⟨263724273660518653662900953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175816182440345769108600635 263724273660518653662900953)
      ·
        refine ⟨197793205245388990247175715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263724273660518653662900953 197793205245388990247175715)
        ·
          refine ⟨296689807868083485370763573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197793205245388990247175715 296689807868083485370763573)
          ·
            refine ⟨27814669487632826753509085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296689807868083485370763573 27814669487632826753509085)
            ·
              refine ⟨10430501057862310032565907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27814669487632826753509085 10430501057862310032565907)
              ·
                refine ⟨15645751586793465048848861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430501057862310032565907 15645751586793465048848861)
                ·
                  refine ⟨5867156845047549393318323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15645751586793465048848861 5867156845047549393318323)
                  ·
                    refine ⟨8800735267571324089977485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867156845047549393318323 8800735267571324089977485)
                    ·
                      refine ⟨3300275725339246533741557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800735267571324089977485 3300275725339246533741557)
                      ·
                        rfl

theorem cell23_6427264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_6427264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427264 prefixEnd_6427264 := by exact prefixLift 6427264
  have htrace : WordTrace (prefixWord ++ tailWord_6427264) baseStart_6427264 baseEnd_6427264 := by
    simpa [prefixWord, tailWord_6427264, baseEnd_6427264] using wordTrace_append hprefix tailTrace_6427264
  have hstable : (prefixWord ++ tailWord_6427264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427264).length < 2 ^ (prefixWord ++ tailWord_6427264).sum := by decide
  have hdescent : baseEnd_6427264 < baseStart_6427264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427284 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6427284 : Nat := 118140960795 + 6427284 * 2 ^ 59
def prefixEnd_6427284 : Nat := 4983230072969 + 3 ^ 40 * 6427284 * 2
def baseEnd_6427284 : Nat := 1100095331650778818497155

theorem tailTrace_6427284 : CollatzResearch.WordTrace tailWord_6427284 prefixEnd_6427284 1100095331650778818497155 := by
  unfold tailWord_6427284
  simp only [CollatzResearch.WordTrace]
  refine ⟨117211153023527617780264453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156281537364703490373685937 117211153023527617780264453)
  ·
    refine ⟨21977091191911428333799585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117211153023527617780264453 21977091191911428333799585)
    ·
      refine ⟨16482818393933571250349689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21977091191911428333799585 16482818393933571250349689)
      ·
        refine ⟨12362113795450178437762267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16482818393933571250349689 12362113795450178437762267)
        ·
          refine ⟨18543170693175267656643401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12362113795450178437762267 18543170693175267656643401)
          ·
            refine ⟨13907378019881450742482551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18543170693175267656643401 13907378019881450742482551)
            ·
              refine ⟨20861067029822176113723827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907378019881450742482551 20861067029822176113723827)
              ·
                refine ⟨31291600544733264170585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20861067029822176113723827 31291600544733264170585741)
                ·
                  refine ⟨11734350204274974063969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31291600544733264170585741 11734350204274974063969653)
                  ·
                    refine ⟨1100095331650778818497155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11734350204274974063969653 1100095331650778818497155)
                    ·
                      rfl

theorem cell23_6427284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6427284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427284 prefixEnd_6427284 := by exact prefixLift 6427284
  have htrace : WordTrace (prefixWord ++ tailWord_6427284) baseStart_6427284 baseEnd_6427284 := by
    simpa [prefixWord, tailWord_6427284, baseEnd_6427284] using wordTrace_append hprefix tailTrace_6427284
  have hstable : (prefixWord ++ tailWord_6427284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427284).length < 2 ^ (prefixWord ++ tailWord_6427284).sum := by decide
  have hdescent : baseEnd_6427284 < baseStart_6427284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427287 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6427287 : Nat := 118140960795 + 6427287 * 2 ^ 59
def prefixEnd_6427287 : Nat := 4983230072969 + 3 ^ 40 * 6427287 * 2
def baseEnd_6427287 : Nat := 3300287535394299943753951

theorem tailTrace_6427287 : CollatzResearch.WordTrace tailWord_6427287 prefixEnd_6427287 3300287535394299943753951 := by
  unfold tailWord_6427287
  simp only [CollatzResearch.WordTrace]
  refine ⟨234422415466044367072888115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156281610310696244715258743 234422415466044367072888115)
  ·
    refine ⟨351633623199066550609332173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234422415466044367072888115 351633623199066550609332173)
    ·
      refine ⟨131862608699649956478499565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351633623199066550609332173 131862608699649956478499565)
      ·
        refine ⟨49448478262368733679437337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131862608699649956478499565 49448478262368733679437337)
        ·
          refine ⟨37086358696776550259578003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49448478262368733679437337 37086358696776550259578003)
          ·
            refine ⟨55629538045164825389367005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37086358696776550259578003 55629538045164825389367005)
            ·
              refine ⟨20861076766936809521012627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55629538045164825389367005 20861076766936809521012627)
              ·
                refine ⟨31291615150405214281518941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20861076766936809521012627 31291615150405214281518941)
                ·
                  refine ⟨11734355681401955355569603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31291615150405214281518941 11734355681401955355569603)
                  ·
                    refine ⟨17601533522102933033354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11734355681401955355569603 17601533522102933033354405)
                    ·
                      refine ⟨3300287535394299943753951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17601533522102933033354405 3300287535394299943753951)
                      ·
                        rfl

theorem cell23_6427287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6427287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427287 prefixEnd_6427287 := by exact prefixLift 6427287
  have htrace : WordTrace (prefixWord ++ tailWord_6427287) baseStart_6427287 baseEnd_6427287 := by
    simpa [prefixWord, tailWord_6427287, baseEnd_6427287] using wordTrace_append hprefix tailTrace_6427287
  have hstable : (prefixWord ++ tailWord_6427287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427287).length < 2 ^ (prefixWord ++ tailWord_6427287).sum := by decide
  have hdescent : baseEnd_6427287 < baseStart_6427287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427327 : List Nat := [1, 1, 2, 2, 2, 6, 1, 8]
def baseStart_6427327 : Nat := 118140960795 + 6427327 * 2 ^ 59
def prefixEnd_6427327 : Nat := 4983230072969 + 3 ^ 40 * 6427327 * 2
def baseEnd_6427327 : Nat := 122233632393351103231621

theorem tailTrace_6427327 : CollatzResearch.WordTrace tailWord_6427327 prefixEnd_6427327 122233632393351103231621 := by
  unfold tailWord_6427327
  simp only [CollatzResearch.WordTrace]
  refine ⟨234423874385899453904344235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156282582923932969269562823 234423874385899453904344235)
  ·
    refine ⟨351635811578849180856516353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234423874385899453904344235 351635811578849180856516353)
    ·
      refine ⟨263726858684136885642387265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351635811578849180856516353 263726858684136885642387265)
      ·
        refine ⟨197795144013102664231790449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263726858684136885642387265 197795144013102664231790449)
        ·
          refine ⟨148346358009826998173842837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197795144013102664231790449 148346358009826998173842837)
          ·
            refine ⟨6953735531710640539398883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148346358009826998173842837 6953735531710640539398883)
            ·
              refine ⟨10430603297565960809098325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953735531710640539398883 10430603297565960809098325)
              ·
                refine ⟨122233632393351103231621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10430603297565960809098325 122233632393351103231621)
                ·
                  rfl

theorem cell23_6427327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 8].length) (baseStart_6427327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427327 prefixEnd_6427327 := by exact prefixLift 6427327
  have htrace : WordTrace (prefixWord ++ tailWord_6427327) baseStart_6427327 baseEnd_6427327 := by
    simpa [prefixWord, tailWord_6427327, baseEnd_6427327] using wordTrace_append hprefix tailTrace_6427327
  have hstable : (prefixWord ++ tailWord_6427327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427327).length < 2 ^ (prefixWord ++ tailWord_6427327).sum := by decide
  have hdescent : baseEnd_6427327 < baseStart_6427327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427354 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_6427354 : Nat := 118140960795 + 6427354 * 2 ^ 59
def prefixEnd_6427354 : Nat := 4983230072969 + 3 ^ 40 * 6427354 * 2
def baseEnd_6427354 : Nat := 3300321938598151181616143

theorem tailTrace_6427354 : CollatzResearch.WordTrace tailWord_6427354 prefixEnd_6427354 3300321938598151181616143 := by
  unfold tailWord_6427354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58606214789200409378894279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156283239437867758343718077 58606214789200409378894279)
  ·
    refine ⟨87909322183800614068341419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58606214789200409378894279 87909322183800614068341419)
    ·
      refine ⟨131863983275700921102512129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87909322183800614068341419 131863983275700921102512129)
      ·
        refine ⟨98897987456775690826884097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131863983275700921102512129 98897987456775690826884097)
        ·
          refine ⟨74173490592581768120163073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98897987456775690826884097 74173490592581768120163073)
          ·
            refine ⟨55630117944436326090122305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74173490592581768120163073 55630117944436326090122305)
            ·
              refine ⟨41722588458327244567591729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55630117944436326090122305 41722588458327244567591729)
              ·
                refine ⟨31291941343745433425693797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41722588458327244567591729 31291941343745433425693797)
                ·
                  refine ⟨5867239001952268767317587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31291941343745433425693797 5867239001952268767317587)
                  ·
                    refine ⟨8800858502928403150976381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867239001952268767317587 8800858502928403150976381)
                    ·
                      refine ⟨3300321938598151181616143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800858502928403150976381 3300321938598151181616143)
                      ·
                        rfl

theorem cell23_6427354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_6427354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427354 prefixEnd_6427354 := by exact prefixLift 6427354
  have htrace : WordTrace (prefixWord ++ tailWord_6427354) baseStart_6427354 baseEnd_6427354 := by
    simpa [prefixWord, tailWord_6427354, baseEnd_6427354] using wordTrace_append hprefix tailTrace_6427354
  have hstable : (prefixWord ++ tailWord_6427354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427354).length < 2 ^ (prefixWord ++ tailWord_6427354).sum := by decide
  have hdescent : baseEnd_6427354 < baseStart_6427354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427388 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_6427388 : Nat := 118140960795 + 6427388 * 2 ^ 59
def prefixEnd_6427388 : Nat := 4983230072969 + 3 ^ 40 * 6427388 * 2
def baseEnd_6427388 : Nat := 3300339396940404048590987

theorem tailTrace_6427388 : CollatzResearch.WordTrace tailWord_6427388 prefixEnd_6427388 3300339396940404048590987 := by
  unfold tailWord_6427388
  simp only [CollatzResearch.WordTrace]
  refine ⟨117213049619339230661157409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156284066159118974214876545 117213049619339230661157409)
  ·
    refine ⟨87909787214504422995868057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117213049619339230661157409 87909787214504422995868057)
    ·
      refine ⟨65932340410878317246901043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87909787214504422995868057 65932340410878317246901043)
      ·
        refine ⟨98898510616317475870351565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65932340410878317246901043 98898510616317475870351565)
        ·
          refine ⟨37086941481119053451381837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98898510616317475870351565 37086941481119053451381837)
          ·
            refine ⟨13907603055419645044268189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37086941481119053451381837 13907603055419645044268189)
            ·
              refine ⟨5215351145782366891600571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13907603055419645044268189 5215351145782366891600571)
              ·
                refine ⟨7823026718673550337400857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215351145782366891600571 7823026718673550337400857)
                ·
                  refine ⟨5867270039005162753050643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823026718673550337400857 5867270039005162753050643)
                  ·
                    refine ⟨8800905058507744129575965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867270039005162753050643 8800905058507744129575965)
                    ·
                      refine ⟨3300339396940404048590987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800905058507744129575965 3300339396940404048590987)
                      ·
                        rfl

theorem cell23_6427388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_6427388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427388 prefixEnd_6427388 := by exact prefixLift 6427388
  have htrace : WordTrace (prefixWord ++ tailWord_6427388) baseStart_6427388 baseEnd_6427388 := by
    simpa [prefixWord, tailWord_6427388, baseEnd_6427388] using wordTrace_append hprefix tailTrace_6427388
  have hstable : (prefixWord ++ tailWord_6427388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427388).length < 2 ^ (prefixWord ++ tailWord_6427388).sum := by decide
  have hdescent : baseEnd_6427388 < baseStart_6427388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427397 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_6427397 : Nat := 118140960795 + 6427397 * 2 ^ 59
def prefixEnd_6427397 : Nat := 4983230072969 + 3 ^ 40 * 6427397 * 2
def baseEnd_6427397 : Nat := 3300344018266294513378445

theorem tailTrace_6427397 : CollatzResearch.WordTrace tailWord_6427397 prefixEnd_6427397 3300344018266294513378445 := by
  unfold tailWord_6427397
  simp only [CollatzResearch.WordTrace]
  refine ⟨234426427495645855859392445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156284284997097237239594963 234426427495645855859392445)
  ·
    refine ⟨87909910310867195947272167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234426427495645855859392445 87909910310867195947272167)
    ·
      refine ⟨131864865466300793920908251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87909910310867195947272167 131864865466300793920908251)
      ·
        refine ⟨197797298199451190881362377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131864865466300793920908251 197797298199451190881362377)
        ·
          refine ⟨148347973649588393161021783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197797298199451190881362377 148347973649588393161021783)
          ·
            refine ⟨222521960474382589741532675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148347973649588393161021783 222521960474382589741532675)
            ·
              refine ⟨333782940711573884612299013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222521960474382589741532675 333782940711573884612299013)
              ·
                refine ⟨62584301383420103364806065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333782940711573884612299013 62584301383420103364806065)
                ·
                  refine ⟨46938226037565077523604549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62584301383420103364806065 46938226037565077523604549)
                  ·
                    refine ⟨8800917382043452035675853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46938226037565077523604549 8800917382043452035675853)
                    ·
                      refine ⟨3300344018266294513378445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8800917382043452035675853 3300344018266294513378445)
                      ·
                        rfl

theorem cell23_6427397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_6427397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427397 prefixEnd_6427397 := by exact prefixLift 6427397
  have htrace : WordTrace (prefixWord ++ tailWord_6427397) baseStart_6427397 baseEnd_6427397 := by
    simpa [prefixWord, tailWord_6427397, baseEnd_6427397] using wordTrace_append hprefix tailTrace_6427397
  have hstable : (prefixWord ++ tailWord_6427397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427397).length < 2 ^ (prefixWord ++ tailWord_6427397).sum := by decide
  have hdescent : baseEnd_6427397 < baseStart_6427397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427445 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_6427445 : Nat := 118140960795 + 6427445 * 2 ^ 59
def prefixEnd_6427445 : Nat := 4983230072969 + 3 ^ 40 * 6427445 * 2
def baseEnd_6427445 : Nat := 3300368665337710325578225

theorem tailTrace_6427445 : CollatzResearch.WordTrace tailWord_6427445 prefixEnd_6427445 3300368665337710325578225 := by
  unfold tailWord_6427445
  simp only [CollatzResearch.WordTrace]
  refine ⟨234428178199471960057139789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156285452132981306704759859 234428178199471960057139789)
  ·
    refine ⟨87910566824801985021427421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234428178199471960057139789 87910566824801985021427421)
    ·
      refine ⟨32966462559300744383035283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87910566824801985021427421 32966462559300744383035283)
      ·
        refine ⟨49449693838951116574552925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32966462559300744383035283 49449693838951116574552925)
        ·
          refine ⟨18543635189606668715457347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49449693838951116574552925 18543635189606668715457347)
          ·
            refine ⟨27815452784410003073186021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18543635189606668715457347 27815452784410003073186021)
            ·
              refine ⟨5215397397076875576222379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27815452784410003073186021 5215397397076875576222379)
              ·
                refine ⟨7823096095615313364333569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215397397076875576222379 7823096095615313364333569)
                ·
                  refine ⟨5867322071711485023250177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823096095615313364333569 5867322071711485023250177)
                  ·
                    refine ⟨4400491553783613767437633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5867322071711485023250177 4400491553783613767437633)
                    ·
                      refine ⟨3300368665337710325578225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400491553783613767437633 3300368665337710325578225)
                      ·
                        rfl

theorem cell23_6427445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_6427445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427445 prefixEnd_6427445 := by exact prefixLift 6427445
  have htrace : WordTrace (prefixWord ++ tailWord_6427445) baseStart_6427445 baseEnd_6427445 := by
    simpa [prefixWord, tailWord_6427445, baseEnd_6427445] using wordTrace_append hprefix tailTrace_6427445
  have hstable : (prefixWord ++ tailWord_6427445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427445).length < 2 ^ (prefixWord ++ tailWord_6427445).sum := by decide
  have hdescent : baseEnd_6427445 < baseStart_6427445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427447 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 4, 5]
def baseStart_6427447 : Nat := 118140960795 + 6427447 * 2 ^ 59
def prefixEnd_6427447 : Nat := 4983230072969 + 3 ^ 40 * 6427447 * 2
def baseEnd_6427447 : Nat := 1100123230766339772584405

theorem tailTrace_6427447 : CollatzResearch.WordTrace tailWord_6427447 prefixEnd_6427447 1100123230766339772584405 := by
  unfold tailWord_6427447
  simp only [CollatzResearch.WordTrace]
  refine ⟨234428251145464714398712595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156285500763643142932475063 234428251145464714398712595)
  ·
    refine ⟨351642376718197071598068893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234428251145464714398712595 351642376718197071598068893)
    ·
      refine ⟨131865891269323901849275835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351642376718197071598068893 131865891269323901849275835)
      ·
        refine ⟨197798836903985852773913753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131865891269323901849275835 197798836903985852773913753)
        ·
          refine ⟨148349127677989389580435315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197798836903985852773913753 148349127677989389580435315)
          ·
            refine ⟨222523691516984084370652973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148349127677989389580435315 222523691516984084370652973)
            ·
              refine ⟨83446384318869031638994865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222523691516984084370652973 83446384318869031638994865)
              ·
                refine ⟨62584788239151773729246149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83446384318869031638994865 62584788239151773729246149)
                ·
                  refine ⟨11734647794840957574233653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62584788239151773729246149 11734647794840957574233653)
                  ·
                    refine ⟨1100123230766339772584405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11734647794840957574233653 1100123230766339772584405)
                    ·
                      rfl

theorem cell23_6427447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_6427447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427447 prefixEnd_6427447 := by exact prefixLift 6427447
  have htrace : WordTrace (prefixWord ++ tailWord_6427447) baseStart_6427447 baseEnd_6427447 := by
    simpa [prefixWord, tailWord_6427447, baseEnd_6427447] using wordTrace_append hprefix tailTrace_6427447
  have hstable : (prefixWord ++ tailWord_6427447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427447).length < 2 ^ (prefixWord ++ tailWord_6427447).sum := by decide
  have hdescent : baseEnd_6427447 < baseStart_6427447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427464 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_6427464 : Nat := 118140960795 + 6427464 * 2 ^ 59
def prefixEnd_6427464 : Nat := 4983230072969 + 3 ^ 40 * 6427464 * 2
def baseEnd_6427464 : Nat := 1100126140490048583746879

theorem tailTrace_6427464 : CollatzResearch.WordTrace tailWord_6427464 prefixEnd_6427464 1100126140490048583746879 := by
  unfold tailWord_6427464
  simp only [CollatzResearch.WordTrace]
  refine ⟨117214435593201563151040723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156285914124268750868054297 117214435593201563151040723)
  ·
    refine ⟨175821653389802344726561085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117214435593201563151040723 175821653389802344726561085)
    ·
      refine ⟨65933120021175879272460407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175821653389802344726561085 65933120021175879272460407)
      ·
        refine ⟨98899680031763818908690611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65933120021175879272460407 98899680031763818908690611)
        ·
          refine ⟨148349520047645728363035917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98899680031763818908690611 148349520047645728363035917)
          ·
            refine ⟨55631070017867148136138469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148349520047645728363035917 55631070017867148136138469)
            ·
              refine ⟨10430825628350090275525963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55631070017867148136138469 10430825628350090275525963)
              ·
                refine ⟨15646238442525135413288945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430825628350090275525963 15646238442525135413288945)
                ·
                  refine ⟨11734678831893851559966709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15646238442525135413288945 11734678831893851559966709)
                  ·
                    refine ⟨1100126140490048583746879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11734678831893851559966709 1100126140490048583746879)
                    ·
                      rfl

theorem cell23_6427464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_6427464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427464 prefixEnd_6427464 := by exact prefixLift 6427464
  have htrace : WordTrace (prefixWord ++ tailWord_6427464) baseStart_6427464 baseEnd_6427464 := by
    simpa [prefixWord, tailWord_6427464, baseEnd_6427464] using wordTrace_append hprefix tailTrace_6427464
  have hstable : (prefixWord ++ tailWord_6427464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427464).length < 2 ^ (prefixWord ++ tailWord_6427464).sum := by decide
  have hdescent : baseEnd_6427464 < baseStart_6427464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427487 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_6427487 : Nat := 118140960795 + 6427487 * 2 ^ 59
def prefixEnd_6427487 : Nat := 4983230072969 + 3 ^ 40 * 6427487 * 2
def baseEnd_6427487 : Nat := 3300390231525199161253031

theorem tailTrace_6427487 : CollatzResearch.WordTrace tailWord_6427487 prefixEnd_6427487 3300390231525199161253031 := by
  unfold tailWord_6427487
  simp only [CollatzResearch.WordTrace]
  refine ⟨234429710065319801230168715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156286473376879867486779143 234429710065319801230168715)
  ·
    refine ⟨351644565097979701845253073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234429710065319801230168715 351644565097979701845253073)
    ·
      refine ⟨263733423823484776383939805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351644565097979701845253073 263733423823484776383939805)
      ·
        refine ⟨98900033933806791143977427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263733423823484776383939805 98900033933806791143977427)
        ·
          refine ⟨148350050900710186715966141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98900033933806791143977427 148350050900710186715966141)
          ·
            refine ⟨55631269087766320018487303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148350050900710186715966141 55631269087766320018487303)
            ·
              refine ⟨83446903631649480027730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55631269087766320018487303 83446903631649480027730955)
              ·
                refine ⟨125170355447474220041596433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83446903631649480027730955 125170355447474220041596433)
                ·
                  refine ⟨93877766585605665031197325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125170355447474220041596433 93877766585605665031197325)
                  ·
                    refine ⟨35204162469602124386698997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93877766585605665031197325 35204162469602124386698997)
                    ·
                      refine ⟨3300390231525199161253031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35204162469602124386698997 3300390231525199161253031)
                      ·
                        rfl

theorem cell23_6427487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_6427487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427487 prefixEnd_6427487 := by exact prefixLift 6427487
  have htrace : WordTrace (prefixWord ++ tailWord_6427487) baseStart_6427487 baseEnd_6427487 := by
    simpa [prefixWord, tailWord_6427487, baseEnd_6427487] using wordTrace_append hprefix tailTrace_6427487
  have hstable : (prefixWord ++ tailWord_6427487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427487).length < 2 ^ (prefixWord ++ tailWord_6427487).sum := by decide
  have hdescent : baseEnd_6427487 < baseStart_6427487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427497 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_6427497 : Nat := 118140960795 + 6427497 * 2 ^ 59
def prefixEnd_6427497 : Nat := 4983230072969 + 3 ^ 40 * 6427497 * 2
def baseEnd_6427497 : Nat := 3300395366331744122127985

theorem tailTrace_6427497 : CollatzResearch.WordTrace tailWord_6427497 prefixEnd_6427497 3300395366331744122127985 := by
  unfold tailWord_6427497
  simp only [CollatzResearch.WordTrace]
  refine ⟨234430074795283572938032745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156286716530189048625355163 234430074795283572938032745)
  ·
    refine ⟨175822556096462679703524559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234430074795283572938032745 175822556096462679703524559)
    ·
      refine ⟨263733834144694019555286839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175822556096462679703524559 263733834144694019555286839)
      ·
        refine ⟨395600751217041029332930259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263733834144694019555286839 395600751217041029332930259)
        ·
          refine ⟨593401126825561543999395389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395600751217041029332930259 593401126825561543999395389)
          ·
            refine ⟨222525422559585578999773271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 593401126825561543999395389 222525422559585578999773271)
            ·
              refine ⟨333788133839378368499659907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222525422559585578999773271 333788133839378368499659907)
              ·
                refine ⟨500682200759067552749489861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333788133839378368499659907 500682200759067552749489861)
                ·
                  refine ⟨93877912642325166140529349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500682200759067552749489861 93877912642325166140529349)
                  ·
                    refine ⟨17602108620435968651349253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93877912642325166140529349 17602108620435968651349253)
                    ·
                      refine ⟨3300395366331744122127985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17602108620435968651349253 3300395366331744122127985)
                      ·
                        rfl

theorem cell23_6427497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_6427497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427497 prefixEnd_6427497 := by exact prefixLift 6427497
  have htrace : WordTrace (prefixWord ++ tailWord_6427497) baseStart_6427497 baseEnd_6427497 := by
    simpa [prefixWord, tailWord_6427497, baseEnd_6427497] using wordTrace_append hprefix tailTrace_6427497
  have hstable : (prefixWord ++ tailWord_6427497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427497).length < 2 ^ (prefixWord ++ tailWord_6427497).sum := by decide
  have hdescent : baseEnd_6427497 < baseStart_6427497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427504 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_6427504 : Nat := 118140960795 + 6427504 * 2 ^ 59
def prefixEnd_6427504 : Nat := 4983230072969 + 3 ^ 40 * 6427504 * 2
def baseEnd_6427504 : Nat := 3300398960696325594740453

theorem tailTrace_6427504 : CollatzResearch.WordTrace tailWord_6427504 prefixEnd_6427504 3300398960696325594740453 := by
  unfold tailWord_6427504
  simp only [CollatzResearch.WordTrace]
  refine ⟨117215165053129106566768783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156286886737505475422358377 117215165053129106566768783)
  ·
    refine ⟨175822747579693659850153175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117215165053129106566768783 175822747579693659850153175)
    ·
      refine ⟨263734121369540489775229763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175822747579693659850153175 263734121369540489775229763)
      ·
        refine ⟨395601182054310734662844645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263734121369540489775229763 395601182054310734662844645)
        ·
          refine ⟨74175221635183262749283371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395601182054310734662844645 74175221635183262749283371)
          ·
            refine ⟨111262832452774894123925057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74175221635183262749283371 111262832452774894123925057)
            ·
              refine ⟨83447124339581170592943793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111262832452774894123925057 83447124339581170592943793)
              ·
                refine ⟨62585343254685877944707845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83447124339581170592943793 62585343254685877944707845)
                ·
                  refine ⟨11734751860253602114632721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62585343254685877944707845 11734751860253602114632721)
                  ·
                    refine ⟨8801063895190201585974541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11734751860253602114632721 8801063895190201585974541)
                    ·
                      refine ⟨3300398960696325594740453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801063895190201585974541 3300398960696325594740453)
                      ·
                        rfl

theorem cell23_6427504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_6427504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427504 prefixEnd_6427504 := by exact prefixLift 6427504
  have htrace : WordTrace (prefixWord ++ tailWord_6427504) baseStart_6427504 baseEnd_6427504 := by
    simpa [prefixWord, tailWord_6427504, baseEnd_6427504] using wordTrace_append hprefix tailTrace_6427504
  have hstable : (prefixWord ++ tailWord_6427504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427504).length < 2 ^ (prefixWord ++ tailWord_6427504).sum := by decide
  have hdescent : baseEnd_6427504 < baseStart_6427504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427518 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6427518 : Nat := 118140960795 + 6427518 * 2 ^ 59
def prefixEnd_6427518 : Nat := 4983230072969 + 3 ^ 40 * 6427518 * 2
def baseEnd_6427518 : Nat := 3300406149425488539965389

theorem tailTrace_6427518 : CollatzResearch.WordTrace tailWord_6427518 prefixEnd_6427518 3300406149425488539965389 := by
  unfold tailWord_6427518
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303855091025936690568401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156287227152138329016364805 29303855091025936690568401)
  ·
    refine ⟨21977891318269452517926301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29303855091025936690568401 21977891318269452517926301)
    ·
      refine ⟨8241709244351044694222363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21977891318269452517926301 8241709244351044694222363)
      ·
        refine ⟨12362563866526567041333545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241709244351044694222363 12362563866526567041333545)
        ·
          refine ⟨9271922899894925281000159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12362563866526567041333545 9271922899894925281000159)
          ·
            refine ⟨13907884349842387921500239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9271922899894925281000159 13907884349842387921500239)
            ·
              refine ⟨20861826524763581882250359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907884349842387921500239 20861826524763581882250359)
              ·
                refine ⟨31292739787145372823375539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20861826524763581882250359 31292739787145372823375539)
                ·
                  refine ⟨46939109680718059235063309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31292739787145372823375539 46939109680718059235063309)
                  ·
                    refine ⟨17602166130269272213148741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46939109680718059235063309 17602166130269272213148741)
                    ·
                      refine ⟨3300406149425488539965389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17602166130269272213148741 3300406149425488539965389)
                      ·
                        rfl

theorem cell23_6427518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6427518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427518 prefixEnd_6427518 := by exact prefixLift 6427518
  have htrace : WordTrace (prefixWord ++ tailWord_6427518) baseStart_6427518 baseEnd_6427518 := by
    simpa [prefixWord, tailWord_6427518, baseEnd_6427518] using wordTrace_append hprefix tailTrace_6427518
  have hstable : (prefixWord ++ tailWord_6427518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427518).length < 2 ^ (prefixWord ++ tailWord_6427518).sum := by decide
  have hdescent : baseEnd_6427518 < baseStart_6427518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427528 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 1, 4]
def baseStart_6427528 : Nat := 118140960795 + 6427528 * 2 ^ 59
def prefixEnd_6427528 : Nat := 4983230072969 + 3 ^ 40 * 6427528 * 2
def baseEnd_6427528 : Nat := 1100137094744011166946781

theorem tailTrace_6427528 : CollatzResearch.WordTrace tailWord_6427528 prefixEnd_6427528 1100137094744011166946781 := by
  unfold tailWord_6427528
  simp only [CollatzResearch.WordTrace]
  refine ⟨117215602729085632616205619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156287470305447510154940825 117215602729085632616205619)
  ·
    refine ⟨175823404093628448924308429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117215602729085632616205619 175823404093628448924308429)
    ·
      refine ⟨65933776535110668346615661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175823404093628448924308429 65933776535110668346615661)
      ·
        refine ⟨24725166200666500629980873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65933776535110668346615661 24725166200666500629980873)
        ·
          refine ⟨18543874650499875472485655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24725166200666500629980873 18543874650499875472485655)
          ·
            refine ⟨27815811975749813208728483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18543874650499875472485655 27815811975749813208728483)
            ·
              refine ⟨41723717963624719813092725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27815811975749813208728483 41723717963624719813092725)
              ·
                refine ⟨3911598559089817482477443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41723717963624719813092725 3911598559089817482477443)
                ·
                  refine ⟨5867397838634726223716165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911598559089817482477443 5867397838634726223716165)
                  ·
                    refine ⟨1100137094744011166946781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5867397838634726223716165 1100137094744011166946781)
                    ·
                      rfl

theorem cell23_6427528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_6427528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427528 prefixEnd_6427528 := by exact prefixLift 6427528
  have htrace : WordTrace (prefixWord ++ tailWord_6427528) baseStart_6427528 baseEnd_6427528 := by
    simpa [prefixWord, tailWord_6427528, baseEnd_6427528] using wordTrace_append hprefix tailTrace_6427528
  have hstable : (prefixWord ++ tailWord_6427528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427528).length < 2 ^ (prefixWord ++ tailWord_6427528).sum := by decide
  have hdescent : baseEnd_6427528 < baseStart_6427528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427541 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 6]
def baseStart_6427541 : Nat := 118140960795 + 6427541 * 2 ^ 59
def prefixEnd_6427541 : Nat := 4983230072969 + 3 ^ 40 * 6427541 * 2
def baseEnd_6427541 : Nat := 366713106608949105553087

theorem tailTrace_6427541 : CollatzResearch.WordTrace tailWord_6427541 prefixEnd_6427541 366713106608949105553087 := by
  unfold tailWord_6427541
  simp only [CollatzResearch.WordTrace]
  refine ⟨234431679607124168452634477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156287786404749445635089651 234431679607124168452634477)
  ·
    refine ⟨87911879852671563169737929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234431679607124168452634477 87911879852671563169737929)
    ·
      refine ⟨65933909889503672377303447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87911879852671563169737929 65933909889503672377303447)
      ·
        refine ⟨98900864834255508565955171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65933909889503672377303447 98900864834255508565955171)
        ·
          refine ⟨148351297251383262848932757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98900864834255508565955171 148351297251383262848932757)
          ·
            refine ⟨6953967058658590446043723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148351297251383262848932757 6953967058658590446043723)
            ·
              refine ⟨10430950587987885669065585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953967058658590446043723 10430950587987885669065585)
              ·
                refine ⟨7823212940990914251799189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10430950587987885669065585 7823212940990914251799189)
                ·
                  refine ⟨366713106608949105553087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7823212940990914251799189 366713106608949105553087)
                  ·
                    rfl

theorem cell23_6427541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_6427541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427541 prefixEnd_6427541 := by exact prefixLift 6427541
  have htrace : WordTrace (prefixWord ++ tailWord_6427541) baseStart_6427541 baseEnd_6427541 := by
    simpa [prefixWord, tailWord_6427541, baseEnd_6427541] using wordTrace_append hprefix tailTrace_6427541
  have hstable : (prefixWord ++ tailWord_6427541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427541).length < 2 ^ (prefixWord ++ tailWord_6427541).sum := by decide
  have hdescent : baseEnd_6427541 < baseStart_6427541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427591 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_6427591 : Nat := 118140960795 + 6427591 * 2 ^ 59
def prefixEnd_6427591 : Nat := 4983230072969 + 3 ^ 40 * 6427591 * 2
def baseEnd_6427591 : Nat := 3300443633513266754352553

theorem tailTrace_6427591 : CollatzResearch.WordTrace tailWord_6427591 prefixEnd_6427591 3300443633513266754352553 := by
  unfold tailWord_6427591
  simp only [CollatzResearch.WordTrace]
  refine ⟨234433503256943026991954627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156289002171295351327969751 234433503256943026991954627)
  ·
    refine ⟨351650254885414540487931941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234433503256943026991954627 351650254885414540487931941)
    ·
      refine ⟨65934422791015226341487239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351650254885414540487931941 65934422791015226341487239)
      ·
        refine ⟨98901634186522839512230859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65934422791015226341487239 98901634186522839512230859)
        ·
          refine ⟨148352451279784259268346289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98901634186522839512230859 148352451279784259268346289)
          ·
            refine ⟨111264338459838194451259717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148352451279784259268346289 111264338459838194451259717)
            ·
              refine ⟨20862063461219661459611197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111264338459838194451259717 20862063461219661459611197)
              ·
                refine ⟨7823273797957373047354199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20862063461219661459611197 7823273797957373047354199)
                ·
                  refine ⟨11734910696936059571031299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823273797957373047354199 11734910696936059571031299)
                  ·
                    refine ⟨17602366045404089356546949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11734910696936059571031299 17602366045404089356546949)
                    ·
                      refine ⟨3300443633513266754352553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17602366045404089356546949 3300443633513266754352553)
                      ·
                        rfl

theorem cell23_6427591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_6427591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427591 prefixEnd_6427591 := by exact prefixLift 6427591
  have htrace : WordTrace (prefixWord ++ tailWord_6427591) baseStart_6427591 baseEnd_6427591 := by
    simpa [prefixWord, tailWord_6427591, baseEnd_6427591] using wordTrace_append hprefix tailTrace_6427591
  have hstable : (prefixWord ++ tailWord_6427591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427591).length < 2 ^ (prefixWord ++ tailWord_6427591).sum := by decide
  have hdescent : baseEnd_6427591 < baseStart_6427591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427601 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_6427601 : Nat := 118140960795 + 6427601 * 2 ^ 59
def prefixEnd_6427601 : Nat := 4983230072969 + 3 ^ 40 * 6427601 * 2
def baseEnd_6427601 : Nat := 1100149589439937238409169

theorem tailTrace_6427601 : CollatzResearch.WordTrace tailWord_6427601 prefixEnd_6427601 1100149589439937238409169 := by
  unfold tailWord_6427601
  simp only [CollatzResearch.WordTrace]
  refine ⟨234433867986906798699818657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156289245324604532466545771 234433867986906798699818657)
  ·
    refine ⟨175825400990180099024863993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234433867986906798699818657 175825400990180099024863993)
    ·
      refine ⟨131869050742635074268647995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175825400990180099024863993 131869050742635074268647995)
      ·
        refine ⟨197803576113952611402971993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131869050742635074268647995 197803576113952611402971993)
        ·
          refine ⟨148352682085464458552228995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197803576113952611402971993 148352682085464458552228995)
          ·
            refine ⟨222529023128196687828343493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148352682085464458552228995 222529023128196687828343493)
            ·
              refine ⟨41724191836536878967814405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222529023128196687828343493 41724191836536878967814405)
              ·
                refine ⟨7823285969350664806465201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41724191836536878967814405 7823285969350664806465201)
                ·
                  refine ⟨5867464477012998604848901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823285969350664806465201 5867464477012998604848901)
                  ·
                    refine ⟨1100149589439937238409169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5867464477012998604848901 1100149589439937238409169)
                    ·
                      rfl

theorem cell23_6427601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_6427601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427601 prefixEnd_6427601 := by exact prefixLift 6427601
  have htrace : WordTrace (prefixWord ++ tailWord_6427601) baseStart_6427601 baseEnd_6427601 := by
    simpa [prefixWord, tailWord_6427601, baseEnd_6427601] using wordTrace_append hprefix tailTrace_6427601
  have hstable : (prefixWord ++ tailWord_6427601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427601).length < 2 ^ (prefixWord ++ tailWord_6427601).sum := by decide
  have hdescent : baseEnd_6427601 < baseStart_6427601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427638 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6427638 : Nat := 118140960795 + 6427638 * 2 ^ 59
def prefixEnd_6427638 : Nat := 4983230072969 + 3 ^ 40 * 6427638 * 2
def baseEnd_6427638 : Nat := 3300467767104028070464837

theorem tailTrace_6427638 : CollatzResearch.WordTrace tailWord_6427638 prefixEnd_6427638 3300467767104028070464837 := by
  unfold tailWord_6427638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652201092985797126182223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156290144991848502679277045 14652201092985797126182223)
  ·
    refine ⟨21978301639478695689273335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652201092985797126182223 21978301639478695689273335)
    ·
      refine ⟨32967452459218043533910003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21978301639478695689273335 32967452459218043533910003)
      ·
        refine ⟨49451178688827065300865005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32967452459218043533910003 49451178688827065300865005)
        ·
          refine ⟨18544192008310149487824377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49451178688827065300865005 18544192008310149487824377)
          ·
            refine ⟨13908144006232612115868283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18544192008310149487824377 13908144006232612115868283)
            ·
              refine ⟨20862216009348918173802425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13908144006232612115868283 20862216009348918173802425)
              ·
                refine ⟨15646662007011688630351819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20862216009348918173802425 15646662007011688630351819)
                ·
                  refine ⟨23469993010517532945527729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15646662007011688630351819 23469993010517532945527729)
                  ·
                    refine ⟨17602494757888149709145797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23469993010517532945527729 17602494757888149709145797)
                    ·
                      refine ⟨3300467767104028070464837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17602494757888149709145797 3300467767104028070464837)
                      ·
                        rfl

theorem cell23_6427638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6427638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427638 prefixEnd_6427638 := by exact prefixLift 6427638
  have htrace : WordTrace (prefixWord ++ tailWord_6427638) baseStart_6427638 baseEnd_6427638 := by
    simpa [prefixWord, tailWord_6427638, baseEnd_6427638] using wordTrace_append hprefix tailTrace_6427638
  have hstable : (prefixWord ++ tailWord_6427638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427638).length < 2 ^ (prefixWord ++ tailWord_6427638).sum := by decide
  have hdescent : baseEnd_6427638 < baseStart_6427638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427641 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_6427641 : Nat := 118140960795 + 6427641 * 2 ^ 59
def prefixEnd_6427641 : Nat := 4983230072969 + 3 ^ 40 * 6427641 * 2
def baseEnd_6427641 : Nat := 3300469307545991558727323

theorem tailTrace_6427641 : CollatzResearch.WordTrace tailWord_6427641 prefixEnd_6427641 3300469307545991558727323 := by
  unfold tailWord_6427641
  simp only [CollatzResearch.WordTrace]
  refine ⟨234435326906761885531274777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156290217937841257020849851 234435326906761885531274777)
  ·
    refine ⟨175826495180071414148456083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234435326906761885531274777 175826495180071414148456083)
    ·
      refine ⟨263739742770107121222684125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175826495180071414148456083 263739742770107121222684125)
      ·
        refine ⟨98902403538790170458506547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263739742770107121222684125 98902403538790170458506547)
        ·
          refine ⟨148353605308185255687759821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98902403538790170458506547 148353605308185255687759821)
          ·
            refine ⟨55632601990569470882909933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148353605308185255687759821 55632601990569470882909933)
            ·
              refine ⟨20862225746463551581091225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55632601990569470882909933 20862225746463551581091225)
              ·
                refine ⟨15646669309847663685818419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20862225746463551581091225 15646669309847663685818419)
                ·
                  refine ⟨23470003964771495528727629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15646669309847663685818419 23470003964771495528727629)
                  ·
                    refine ⟨8801251486789310823272861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23470003964771495528727629 8801251486789310823272861)
                    ·
                      refine ⟨3300469307545991558727323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801251486789310823272861 3300469307545991558727323)
                      ·
                        rfl

theorem cell23_6427641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_6427641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427641 prefixEnd_6427641 := by exact prefixLift 6427641
  have htrace : WordTrace (prefixWord ++ tailWord_6427641) baseStart_6427641 baseEnd_6427641 := by
    simpa [prefixWord, tailWord_6427641, baseEnd_6427641] using wordTrace_append hprefix tailTrace_6427641
  have hstable : (prefixWord ++ tailWord_6427641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427641).length < 2 ^ (prefixWord ++ tailWord_6427641).sum := by decide
  have hdescent : baseEnd_6427641 < baseStart_6427641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427659 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 1, 2, 2]
def baseStart_6427659 : Nat := 118140960795 + 6427659 * 2 ^ 59
def prefixEnd_6427659 : Nat := 4983230072969 + 3 ^ 40 * 6427659 * 2
def baseEnd_6427659 : Nat := 3300478550197772488302241

theorem tailTrace_6427659 : CollatzResearch.WordTrace tailWord_6427659 prefixEnd_6427659 3300478550197772488302241 := by
  unfold tailWord_6427659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234435983420696674605430031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156290655613797783070286687 234435983420696674605430031)
  ·
    refine ⟨351653975131045011908145047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234435983420696674605430031 351653975131045011908145047)
    ·
      refine ⟨527480962696567517862217571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351653975131045011908145047 527480962696567517862217571)
      ·
        refine ⟨791221444044851276793326357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527480962696567517862217571 791221444044851276793326357)
        ·
          refine ⟨37088505189602403599687173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 791221444044851276793326357 37088505189602403599687173)
          ·
            refine ⟨6954094723050450674941345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37088505189602403599687173 6954094723050450674941345)
            ·
              refine ⟨5215571042287838006206009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954094723050450674941345 5215571042287838006206009)
              ·
                refine ⟨3911678281715878504654507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5215571042287838006206009 3911678281715878504654507)
                ·
                  refine ⟨5867517422573817756981761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911678281715878504654507 5867517422573817756981761)
                  ·
                    refine ⟨4400638066930363317736321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5867517422573817756981761 4400638066930363317736321)
                    ·
                      refine ⟨3300478550197772488302241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400638066930363317736321 3300478550197772488302241)
                      ·
                        rfl

theorem cell23_6427659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 2, 2].length) (baseStart_6427659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427659 prefixEnd_6427659 := by exact prefixLift 6427659
  have htrace : WordTrace (prefixWord ++ tailWord_6427659) baseStart_6427659 baseEnd_6427659 := by
    simpa [prefixWord, tailWord_6427659, baseEnd_6427659] using wordTrace_append hprefix tailTrace_6427659
  have hstable : (prefixWord ++ tailWord_6427659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427659).length < 2 ^ (prefixWord ++ tailWord_6427659).sum := by decide
  have hdescent : baseEnd_6427659 < baseStart_6427659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427698 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_6427698 : Nat := 118140960795 + 6427698 * 2 ^ 59
def prefixEnd_6427698 : Nat := 4983230072969 + 3 ^ 40 * 6427698 * 2
def baseEnd_6427698 : Nat := 3300498575943297835714561

theorem tailTrace_6427698 : CollatzResearch.WordTrace tailWord_6427698 prefixEnd_6427698 3300498575943297835714561 := by
  unfold tailWord_6427698
  simp only [CollatzResearch.WordTrace]
  refine ⟨58609351466888846066524937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156291603911703589510733165 58609351466888846066524937)
  ·
    refine ⟨43957013600166634549893703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58609351466888846066524937 43957013600166634549893703)
    ·
      refine ⟨65935520400249951824840555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43957013600166634549893703 65935520400249951824840555)
      ·
        refine ⟨98903280600374927737260833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65935520400249951824840555 98903280600374927737260833)
        ·
          refine ⟨74177460450281195802945625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98903280600374927737260833 74177460450281195802945625)
          ·
            refine ⟨55633095337710896852209219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74177460450281195802945625 55633095337710896852209219)
            ·
              refine ⟨83449643006566345278313829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55633095337710896852209219 83449643006566345278313829)
              ·
                refine ⟨15646808063731189739683843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83449643006566345278313829 15646808063731189739683843)
                ·
                  refine ⟨23470212095596784609525765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15646808063731189739683843 23470212095596784609525765)
                  ·
                    refine ⟨4400664767924397114286081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23470212095596784609525765 4400664767924397114286081)
                    ·
                      refine ⟨3300498575943297835714561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400664767924397114286081 3300498575943297835714561)
                      ·
                        rfl

theorem cell23_6427698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_6427698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427698 prefixEnd_6427698 := by exact prefixLift 6427698
  have htrace : WordTrace (prefixWord ++ tailWord_6427698) baseStart_6427698 baseEnd_6427698 := by
    simpa [prefixWord, tailWord_6427698, baseEnd_6427698] using wordTrace_append hprefix tailTrace_6427698
  have hstable : (prefixWord ++ tailWord_6427698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427698).length < 2 ^ (prefixWord ++ tailWord_6427698).sum := by decide
  have hdescent : baseEnd_6427698 < baseStart_6427698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427702 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6427702 : Nat := 118140960795 + 6427702 * 2 ^ 59
def prefixEnd_6427702 : Nat := 4983230072969 + 3 ^ 40 * 6427702 * 2
def baseEnd_6427702 : Nat := 3300500629865915820064543

theorem tailTrace_6427702 : CollatzResearch.WordTrace tailWord_6427702 prefixEnd_6427702 3300500629865915820064543 := by
  unfold tailWord_6427702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652346984971305809327835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156291701173027261966163573 14652346984971305809327835)
  ·
    refine ⟨21978520477456958713991753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652346984971305809327835 21978520477456958713991753)
    ·
      refine ⟨16483890358092719035493815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21978520477456958713991753 16483890358092719035493815)
      ·
        refine ⟨24725835537139078553240723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16483890358092719035493815 24725835537139078553240723)
        ·
          refine ⟨37088753305708617829861085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24725835537139078553240723 37088753305708617829861085)
          ·
            refine ⟨13908282489640731686197907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37088753305708617829861085 13908282489640731686197907)
            ·
              refine ⟨20862423734461097529296861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13908282489640731686197907 20862423734461097529296861)
              ·
                refine ⟨7823408900422911573486323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20862423734461097529296861 7823408900422911573486323)
                ·
                  refine ⟨11735113350634367360229485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823408900422911573486323 11735113350634367360229485)
                  ·
                    refine ⟨4400667506487887760086057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11735113350634367360229485 4400667506487887760086057)
                    ·
                      refine ⟨3300500629865915820064543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400667506487887760086057 3300500629865915820064543)
                      ·
                        rfl

theorem cell23_6427702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6427702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427702 prefixEnd_6427702 := by exact prefixLift 6427702
  have htrace : WordTrace (prefixWord ++ tailWord_6427702) baseStart_6427702 baseEnd_6427702 := by
    simpa [prefixWord, tailWord_6427702, baseEnd_6427702] using wordTrace_append hprefix tailTrace_6427702
  have hstable : (prefixWord ++ tailWord_6427702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427702).length < 2 ^ (prefixWord ++ tailWord_6427702).sum := by decide
  have hdescent : baseEnd_6427702 < baseStart_6427702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427751 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6427751 : Nat := 118140960795 + 6427751 * 2 ^ 59
def prefixEnd_6427751 : Nat := 4983230072969 + 3 ^ 40 * 6427751 * 2
def baseEnd_6427751 : Nat := 1100175263472662042783939

theorem tailTrace_6427751 : CollatzResearch.WordTrace tailWord_6427751 prefixEnd_6427751 1100175263472662042783939 := by
  unfold tailWord_6427751
  simp only [CollatzResearch.WordTrace]
  refine ⟨234439338936363374317779107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156292892624242249545186071 234439338936363374317779107)
  ·
    refine ⟨351659008404545061476668661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234439338936363374317779107 351659008404545061476668661)
    ·
      refine ⟨32968032037926099513437687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351659008404545061476668661 32968032037926099513437687)
      ·
        refine ⟨49452048056889149270156531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32968032037926099513437687 49452048056889149270156531)
        ·
          refine ⟨74178072085333723905234797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49452048056889149270156531 74178072085333723905234797)
          ·
            refine ⟨27816777032000146464463049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74178072085333723905234797 27816777032000146464463049)
            ·
              refine ⟨20862582774000109848347287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27816777032000146464463049 20862582774000109848347287)
              ·
                refine ⟨31293874161000164772520931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20862582774000109848347287 31293874161000164772520931)
                ·
                  refine ⟨46940811241500247158781397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31293874161000164772520931 46940811241500247158781397)
                  ·
                    refine ⟨1100175263472662042783939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46940811241500247158781397 1100175263472662042783939)
                    ·
                      rfl

theorem cell23_6427751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6427751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427751 prefixEnd_6427751 := by exact prefixLift 6427751
  have htrace : WordTrace (prefixWord ++ tailWord_6427751) baseStart_6427751 baseEnd_6427751 := by
    simpa [prefixWord, tailWord_6427751, baseEnd_6427751] using wordTrace_append hprefix tailTrace_6427751
  have hstable : (prefixWord ++ tailWord_6427751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427751).length < 2 ^ (prefixWord ++ tailWord_6427751).sum := by decide
  have hdescent : baseEnd_6427751 < baseStart_6427751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427788 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_6427788 : Nat := 118140960795 + 6427788 * 2 ^ 59
def prefixEnd_6427788 : Nat := 4983230072969 + 3 ^ 40 * 6427788 * 2
def baseEnd_6427788 : Nat := 3300544789202202483589147

theorem tailTrace_6427788 : CollatzResearch.WordTrace tailWord_6427788 prefixEnd_6427788 3300544789202202483589147 := by
  unfold tailWord_6427788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117220344218614664818438009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156293792291486219757917345 117220344218614664818438009)
  ·
    refine ⟨87915258163960998613828507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117220344218614664818438009 87915258163960998613828507)
    ·
      refine ⟨131872887245941497920742761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87915258163960998613828507 131872887245941497920742761)
      ·
        refine ⟨98904665434456123440557071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131872887245941497920742761 98904665434456123440557071)
        ·
          refine ⟨148356998151684185160835607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98904665434456123440557071 148356998151684185160835607)
          ·
            refine ⟨222535497227526277741253411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148356998151684185160835607 222535497227526277741253411)
            ·
              refine ⟨333803245841289416611880117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222535497227526277741253411 333803245841289416611880117)
              ·
                refine ⟨31294054297620882807363761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 333803245841289416611880117 31294054297620882807363761)
                ·
                  refine ⟨23470540723215662105522821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31294054297620882807363761 23470540723215662105522821)
                  ·
                    refine ⟨4400726385602936644785529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23470540723215662105522821 4400726385602936644785529)
                    ·
                      refine ⟨3300544789202202483589147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400726385602936644785529 3300544789202202483589147)
                      ·
                        rfl

theorem cell23_6427788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_6427788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427788 prefixEnd_6427788 := by exact prefixLift 6427788
  have htrace : WordTrace (prefixWord ++ tailWord_6427788) baseStart_6427788 baseEnd_6427788 := by
    simpa [prefixWord, tailWord_6427788, baseEnd_6427788] using wordTrace_append hprefix tailTrace_6427788
  have hstable : (prefixWord ++ tailWord_6427788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427788).length < 2 ^ (prefixWord ++ tailWord_6427788).sum := by decide
  have hdescent : baseEnd_6427788 < baseStart_6427788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427825 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6427825 : Nat := 118140960795 + 6427825 * 2 ^ 59
def prefixEnd_6427825 : Nat := 4983230072969 + 3 ^ 40 * 6427825 * 2
def baseEnd_6427825 : Nat := 3300563787986418838826477

theorem tailTrace_6427825 : CollatzResearch.WordTrace tailWord_6427825 prefixEnd_6427825 3300563787986418838826477 := by
  unfold tailWord_6427825
  simp only [CollatzResearch.WordTrace]
  refine ⟨234442037938095284955972929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156294691958730189970648619 234442037938095284955972929)
  ·
    refine ⟨175831528453571463716979697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234442037938095284955972929 175831528453571463716979697)
    ·
      refine ⟨131873646340178597787734773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175831528453571463716979697 131873646340178597787734773)
      ·
        refine ⟨12363154344391743542600135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131873646340178597787734773 12363154344391743542600135)
        ·
          refine ⟨18544731516587615313900203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12363154344391743542600135 18544731516587615313900203)
          ·
            refine ⟨27817097274881422970850305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18544731516587615313900203 27817097274881422970850305)
            ·
              refine ⟨20862822956161067228137729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27817097274881422970850305 20862822956161067228137729)
              ·
                refine ⟨15647117217120800421103297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20862822956161067228137729 15647117217120800421103297)
                ·
                  refine ⟨11735337912840600315827473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15647117217120800421103297 11735337912840600315827473)
                  ·
                    refine ⟨8801503434630450236870605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11735337912840600315827473 8801503434630450236870605)
                    ·
                      refine ⟨3300563787986418838826477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801503434630450236870605 3300563787986418838826477)
                      ·
                        rfl

theorem cell23_6427825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6427825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427825 prefixEnd_6427825 := by exact prefixLift 6427825
  have htrace : WordTrace (prefixWord ++ tailWord_6427825) baseStart_6427825 baseEnd_6427825 := by
    simpa [prefixWord, tailWord_6427825, baseEnd_6427825] using wordTrace_append hprefix tailTrace_6427825
  have hstable : (prefixWord ++ tailWord_6427825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427825).length < 2 ^ (prefixWord ++ tailWord_6427825).sum := by decide
  have hdescent : baseEnd_6427825 < baseStart_6427825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427831 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_6427831 : Nat := 118140960795 + 6427831 * 2 ^ 59
def prefixEnd_6427831 : Nat := 4983230072969 + 3 ^ 40 * 6427831 * 2
def baseEnd_6427831 : Nat := 3300566868870345815351449

theorem tailTrace_6427831 : CollatzResearch.WordTrace tailWord_6427831 prefixEnd_6427831 3300566868870345815351449 := by
  unfold tailWord_6427831
  simp only [CollatzResearch.WordTrace]
  refine ⟨234442256776073547980691347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156294837850715698653794231 234442256776073547980691347)
  ·
    refine ⟨351663385164110321971037021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234442256776073547980691347 351663385164110321971037021)
    ·
      refine ⟨131873769436541370739138883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351663385164110321971037021 131873769436541370739138883)
      ·
        refine ⟨197810654154812056108708325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131873769436541370739138883 197810654154812056108708325)
        ·
          refine ⟨37089497654027260520382811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197810654154812056108708325 37089497654027260520382811)
          ·
            refine ⟨55634246481040890780574217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37089497654027260520382811 55634246481040890780574217)
            ·
              refine ⟨41725684860780668085430663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55634246481040890780574217 41725684860780668085430663)
              ·
                refine ⟨62588527291171002128145995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41725684860780668085430663 62588527291171002128145995)
                ·
                  refine ⟨93882790936756503192218993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62588527291171002128145995 93882790936756503192218993)
                  ·
                    refine ⟨70412093202567377394164245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93882790936756503192218993 70412093202567377394164245)
                    ·
                      refine ⟨3300566868870345815351449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70412093202567377394164245 3300566868870345815351449)
                      ·
                        rfl

theorem cell23_6427831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_6427831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427831 prefixEnd_6427831 := by exact prefixLift 6427831
  have htrace : WordTrace (prefixWord ++ tailWord_6427831) baseStart_6427831 baseEnd_6427831 := by
    simpa [prefixWord, tailWord_6427831, baseEnd_6427831] using wordTrace_append hprefix tailTrace_6427831
  have hstable : (prefixWord ++ tailWord_6427831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427831).length < 2 ^ (prefixWord ++ tailWord_6427831).sum := by decide
  have hdescent : baseEnd_6427831 < baseStart_6427831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427858 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6427858 : Nat := 118140960795 + 6427858 * 2 ^ 59
def prefixEnd_6427858 : Nat := 4983230072969 + 3 ^ 40 * 6427858 * 2
def baseEnd_6427858 : Nat := 1100193577616005736571275

theorem tailTrace_6427858 : CollatzResearch.WordTrace tailWord_6427858 prefixEnd_6427858 1100193577616005736571275 := by
  unfold tailWord_6427858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58610810386743932897981057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156295494364650487727949485 58610810386743932897981057)
  ·
    refine ⟨43958107790057949673485793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58610810386743932897981057 43958107790057949673485793)
    ·
      refine ⟨32968580842543462255114345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43958107790057949673485793 32968580842543462255114345)
      ·
        refine ⟨24726435631907596691335759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32968580842543462255114345 24726435631907596691335759)
        ·
          refine ⟨37089653447861395037003639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24726435631907596691335759 37089653447861395037003639)
          ·
            refine ⟨55634480171792092555505459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37089653447861395037003639 55634480171792092555505459)
            ·
              refine ⟨83451720257688138833258189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55634480171792092555505459 83451720257688138833258189)
              ·
                refine ⟨31294395096633052062471821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83451720257688138833258189 31294395096633052062471821)
                ·
                  refine ⟨11735398161237394523426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31294395096633052062471821 11735398161237394523426933)
                  ·
                    refine ⟨1100193577616005736571275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11735398161237394523426933 1100193577616005736571275)
                    ·
                      rfl

theorem cell23_6427858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6427858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427858 prefixEnd_6427858 := by exact prefixLift 6427858
  have htrace : WordTrace (prefixWord ++ tailWord_6427858) baseStart_6427858 baseEnd_6427858 := by
    simpa [prefixWord, tailWord_6427858, baseEnd_6427858] using wordTrace_append hprefix tailTrace_6427858
  have hstable : (prefixWord ++ tailWord_6427858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427858).length < 2 ^ (prefixWord ++ tailWord_6427858).sum := by decide
  have hdescent : baseEnd_6427858 < baseStart_6427858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427872 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 1, 1, 3]
def baseStart_6427872 : Nat := 118140960795 + 6427872 * 2 ^ 59
def prefixEnd_6427872 : Nat := 4983230072969 + 3 ^ 40 * 6427872 * 2
def baseEnd_6427872 : Nat := 3300587921577180154938761

theorem tailTrace_6427872 : CollatzResearch.WordTrace tailWord_6427872 prefixEnd_6427872 3300587921577180154938761 := by
  unfold tailWord_6427872
  simp only [CollatzResearch.WordTrace]
  refine ⟨117221876084462505991466935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156295834779283341321955913 117221876084462505991466935)
  ·
    refine ⟨175832814126693758987200403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117221876084462505991466935 175832814126693758987200403)
    ·
      refine ⟨263749221190040638480800605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175832814126693758987200403 263749221190040638480800605)
      ·
        refine ⟨98905957946265239430300227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263749221190040638480800605 98905957946265239430300227)
        ·
          refine ⟨148358936919397859145450341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98905957946265239430300227 148358936919397859145450341)
          ·
            refine ⟨27817300672387098589771939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148358936919397859145450341 27817300672387098589771939)
            ·
              refine ⟨41725951008580647884657909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27817300672387098589771939 41725951008580647884657909)
              ·
                refine ⟨3911807907054435739186679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41725951008580647884657909 3911807907054435739186679)
                ·
                  refine ⟨5867711860581653608780019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911807907054435739186679 5867711860581653608780019)
                  ·
                    refine ⟨8801567790872480413170029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867711860581653608780019 8801567790872480413170029)
                    ·
                      refine ⟨3300587921577180154938761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801567790872480413170029 3300587921577180154938761)
                      ·
                        rfl

theorem cell23_6427872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_6427872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427872 prefixEnd_6427872 := by exact prefixLift 6427872
  have htrace : WordTrace (prefixWord ++ tailWord_6427872) baseStart_6427872 baseEnd_6427872 := by
    simpa [prefixWord, tailWord_6427872, baseEnd_6427872] using wordTrace_append hprefix tailTrace_6427872
  have hstable : (prefixWord ++ tailWord_6427872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427872).length < 2 ^ (prefixWord ++ tailWord_6427872).sum := by decide
  have hdescent : baseEnd_6427872 < baseStart_6427872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_6427895 : Nat := 118140960795 + 6427895 * 2 ^ 59
def prefixEnd_6427895 : Nat := 4983230072969 + 3 ^ 40 * 6427895 * 2
def baseEnd_6427895 : Nat := 3300599731632233564951155

theorem tailTrace_6427895 : CollatzResearch.WordTrace tailWord_6427895 prefixEnd_6427895 3300599731632233564951155 := by
  unfold tailWord_6427895
  simp only [CollatzResearch.WordTrace]
  refine ⟨234444591047841686911021139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156296394031894457940680759 234444591047841686911021139)
  ·
    refine ⟨351666886571762530366531709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234444591047841686911021139 351666886571762530366531709)
    ·
      refine ⟨131875082464410948887449391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351666886571762530366531709 131875082464410948887449391)
      ·
        refine ⟨197812623696616423331174087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131875082464410948887449391 197812623696616423331174087)
        ·
          refine ⟨296718935544924634996761131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197812623696616423331174087 296718935544924634996761131)
          ·
            refine ⟨445078403317386952495141697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296718935544924634996761131 445078403317386952495141697)
            ·
              refine ⟨333808802488040214371356273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445078403317386952495141697 333808802488040214371356273)
              ·
                refine ⟨250356601866030160778517205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333808802488040214371356273 250356601866030160778517205)
                ·
                  refine ⟨5867732856235081893246497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250356601866030160778517205 5867732856235081893246497)
                  ·
                    refine ⟨4400799642176311419934873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5867732856235081893246497 4400799642176311419934873)
                    ·
                      refine ⟨3300599731632233564951155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400799642176311419934873 3300599731632233564951155)
                      ·
                        rfl

theorem cell23_6427895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_6427895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427895 prefixEnd_6427895 := by exact prefixLift 6427895
  have htrace : WordTrace (prefixWord ++ tailWord_6427895) baseStart_6427895 baseEnd_6427895 := by
    simpa [prefixWord, tailWord_6427895, baseEnd_6427895] using wordTrace_append hprefix tailTrace_6427895
  have hstable : (prefixWord ++ tailWord_6427895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427895).length < 2 ^ (prefixWord ++ tailWord_6427895).sum := by decide
  have hdescent : baseEnd_6427895 < baseStart_6427895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427898 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_6427898 : Nat := 118140960795 + 6427898 * 2 ^ 59
def prefixEnd_6427898 : Nat := 4983230072969 + 3 ^ 40 * 6427898 * 2
def baseEnd_6427898 : Nat := 3300601272074197053213641

theorem tailTrace_6427898 : CollatzResearch.WordTrace tailWord_6427898 prefixEnd_6427898 3300601272074197053213641 := by
  unfold tailWord_6427898
  simp only [CollatzResearch.WordTrace]
  refine ⟨58611175116707704605845087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156296466977887212282253565 58611175116707704605845087)
  ·
    refine ⟨87916762675061556908767631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58611175116707704605845087 87916762675061556908767631)
    ·
      refine ⟨131875144012592335363151447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87916762675061556908767631 131875144012592335363151447)
      ·
        refine ⟨197812716018888503044727171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131875144012592335363151447 197812716018888503044727171)
        ·
          refine ⟨296719074028332754567090757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197812716018888503044727171 296719074028332754567090757)
          ·
            refine ⟨55634826380312391481329517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296719074028332754567090757 55634826380312391481329517)
            ·
              refine ⟨20863059892617146805498569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55634826380312391481329517 20863059892617146805498569)
              ·
                refine ⟨15647294919462860104123927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20863059892617146805498569 15647294919462860104123927)
                ·
                  refine ⟨23470942379194290156185891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15647294919462860104123927 23470942379194290156185891)
                  ·
                    refine ⟨35206413568791435234278837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23470942379194290156185891 35206413568791435234278837)
                    ·
                      refine ⟨3300601272074197053213641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35206413568791435234278837 3300601272074197053213641)
                      ·
                        rfl

theorem cell23_6427898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_6427898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427898 prefixEnd_6427898 := by exact prefixLift 6427898
  have htrace : WordTrace (prefixWord ++ tailWord_6427898) baseStart_6427898 baseEnd_6427898 := by
    simpa [prefixWord, tailWord_6427898, baseEnd_6427898] using wordTrace_append hprefix tailTrace_6427898
  have hstable : (prefixWord ++ tailWord_6427898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427898).length < 2 ^ (prefixWord ++ tailWord_6427898).sum := by decide
  have hdescent : baseEnd_6427898 < baseStart_6427898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427905 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6427905 : Nat := 118140960795 + 6427905 * 2 ^ 59
def prefixEnd_6427905 : Nat := 4983230072969 + 3 ^ 40 * 6427905 * 2
def baseEnd_6427905 : Nat := 1100201622146259508608703

theorem tailTrace_6427905 : CollatzResearch.WordTrace tailWord_6427905 prefixEnd_6427905 1100201622146259508608703 := by
  unfold tailWord_6427905
  simp only [CollatzResearch.WordTrace]
  refine ⟨234444955777805458618885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156296637185203639079256779 234444955777805458618885169)
  ·
    refine ⟨175833716833354093964163877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234444955777805458618885169 175833716833354093964163877)
    ·
      refine ⟨32968821906253892618280727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175833716833354093964163877 32968821906253892618280727)
      ·
        refine ⟨49453232859380838927421091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32968821906253892618280727 49453232859380838927421091)
        ·
          refine ⟨74179849289071258391131637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49453232859380838927421091 74179849289071258391131637)
          ·
            refine ⟨6954360870850430474168591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74179849289071258391131637 6954360870850430474168591)
            ·
              refine ⟨10431541306275645711252887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954360870850430474168591 10431541306275645711252887)
              ·
                refine ⟨15647311959413468566879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10431541306275645711252887 15647311959413468566879331)
                ·
                  refine ⟨23470967939120202850318997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15647311959413468566879331 23470967939120202850318997)
                  ·
                    refine ⟨1100201622146259508608703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23470967939120202850318997 1100201622146259508608703)
                    ·
                      rfl

theorem cell23_6427905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6427905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427905 prefixEnd_6427905 := by exact prefixLift 6427905
  have htrace : WordTrace (prefixWord ++ tailWord_6427905) baseStart_6427905 baseEnd_6427905 := by
    simpa [prefixWord, tailWord_6427905, baseEnd_6427905] using wordTrace_append hprefix tailTrace_6427905
  have hstable : (prefixWord ++ tailWord_6427905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427905).length < 2 ^ (prefixWord ++ tailWord_6427905).sum := by decide
  have hdescent : baseEnd_6427905 < baseStart_6427905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427912 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_6427912 : Nat := 118140960795 + 6427912 * 2 ^ 59
def prefixEnd_6427912 : Nat := 4983230072969 + 3 ^ 40 * 6427912 * 2
def baseEnd_6427912 : Nat := 3300608460803359998438577

theorem tailTrace_6427912 : CollatzResearch.WordTrace tailWord_6427912 prefixEnd_6427912 3300608460803359998438577 := by
  unfold tailWord_6427912
  simp only [CollatzResearch.WordTrace]
  refine ⟨117222605544390049407194995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156296807392520065876259993 117222605544390049407194995)
  ·
    refine ⟨175833908316585074110792493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117222605544390049407194995 175833908316585074110792493)
    ·
      refine ⟨65937715618719402791547185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175833908316585074110792493 65937715618719402791547185)
      ·
        refine ⟨49453286714039552093660389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65937715618719402791547185 49453286714039552093660389)
        ·
          refine ⟨9272491258882416017561323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49453286714039552093660389 9272491258882416017561323)
          ·
            refine ⟨13908736888323624026341985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9272491258882416017561323 13908736888323624026341985)
            ·
              refine ⟨10431552666242718019756489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13908736888323624026341985 10431552666242718019756489)
              ·
                refine ⟨7823664499682038514817367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10431552666242718019756489 7823664499682038514817367)
                ·
                  refine ⟨11735496749523057772226051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823664499682038514817367 11735496749523057772226051)
                  ·
                    refine ⟨17603245124284586658339077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11735496749523057772226051 17603245124284586658339077)
                    ·
                      refine ⟨3300608460803359998438577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17603245124284586658339077 3300608460803359998438577)
                      ·
                        rfl

theorem cell23_6427912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_6427912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427912 prefixEnd_6427912 := by exact prefixLift 6427912
  have htrace : WordTrace (prefixWord ++ tailWord_6427912) baseStart_6427912 baseEnd_6427912 := by
    simpa [prefixWord, tailWord_6427912, baseEnd_6427912] using wordTrace_append hprefix tailTrace_6427912
  have hstable : (prefixWord ++ tailWord_6427912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427912).length < 2 ^ (prefixWord ++ tailWord_6427912).sum := by decide
  have hdescent : baseEnd_6427912 < baseStart_6427912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427915 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 3]
def baseStart_6427915 : Nat := 118140960795 + 6427915 * 2 ^ 59
def prefixEnd_6427915 : Nat := 4983230072969 + 3 ^ 40 * 6427915 * 2
def baseEnd_6427915 : Nat := 3300610001245323486701063

theorem tailTrace_6427915 : CollatzResearch.WordTrace tailWord_6427915 prefixEnd_6427915 3300610001245323486701063 := by
  unfold tailWord_6427915
  simp only [CollatzResearch.WordTrace]
  refine ⟨234445320507769230326749199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156296880338512820217832799 234445320507769230326749199)
  ·
    refine ⟨351667980761653845490123799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234445320507769230326749199 351667980761653845490123799)
    ·
      refine ⟨527501971142480768235185699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351667980761653845490123799 527501971142480768235185699)
      ·
        refine ⟨791252956713721152352778549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527501971142480768235185699 791252956713721152352778549)
        ·
          refine ⟨74179964691911358033072989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 791252956713721152352778549 74179964691911358033072989)
          ·
            refine ⟨27817486759466759262402371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74179964691911358033072989 27817486759466759262402371)
            ·
              refine ⟨41726230139200138893603557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27817486759466759262402371 41726230139200138893603557)
              ·
                refine ⟨7823668151100026042550667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41726230139200138893603557 7823668151100026042550667)
                ·
                  refine ⟨11735502226650039063826001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823668151100026042550667 11735502226650039063826001)
                  ·
                    refine ⟨8801626669987529297869501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11735502226650039063826001 8801626669987529297869501)
                    ·
                      refine ⟨3300610001245323486701063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801626669987529297869501 3300610001245323486701063)
                      ·
                        rfl

theorem cell23_6427915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 3].length) (baseStart_6427915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427915 prefixEnd_6427915 := by exact prefixLift 6427915
  have htrace : WordTrace (prefixWord ++ tailWord_6427915) baseStart_6427915 baseEnd_6427915 := by
    simpa [prefixWord, tailWord_6427915, baseEnd_6427915] using wordTrace_append hprefix tailTrace_6427915
  have hstable : (prefixWord ++ tailWord_6427915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427915).length < 2 ^ (prefixWord ++ tailWord_6427915).sum := by decide
  have hdescent : baseEnd_6427915 < baseStart_6427915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427918 : List Nat := [4, 1, 1, 2, 1, 4, 1, 9]
def baseStart_6427918 : Nat := 118140960795 + 6427918 * 2 ^ 59
def prefixEnd_6427918 : Nat := 4983230072969 + 3 ^ 40 * 6427918 * 2
def baseEnd_6427918 : Nat := 122244871914343962035687

theorem tailTrace_6427918 : CollatzResearch.WordTrace tailWord_6427918 prefixEnd_6427918 122244871914343962035687 := by
  unfold tailWord_6427918
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305678740844795229888551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156296953284505574559405605 29305678740844795229888551)
  ·
    refine ⟨43958518111267192844832827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29305678740844795229888551 43958518111267192844832827)
    ·
      refine ⟨65937777166900789267249241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43958518111267192844832827 65937777166900789267249241)
      ·
        refine ⟨49453332875175591950436931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65937777166900789267249241 49453332875175591950436931)
        ·
          refine ⟨74179999312763387925655397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49453332875175591950436931 74179999312763387925655397)
          ·
            refine ⟨13908749871143135236060387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74179999312763387925655397 13908749871143135236060387)
            ·
              refine ⟨20863124806714702854090581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13908749871143135236060387 20863124806714702854090581)
              ·
                refine ⟨122244871914343962035687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20863124806714702854090581 122244871914343962035687)
                ·
                  rfl

theorem cell23_6427918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_6427918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427918 prefixEnd_6427918 := by exact prefixLift 6427918
  have htrace : WordTrace (prefixWord ++ tailWord_6427918) baseStart_6427918 baseEnd_6427918 := by
    simpa [prefixWord, tailWord_6427918, baseEnd_6427918] using wordTrace_append hprefix tailTrace_6427918
  have hstable : (prefixWord ++ tailWord_6427918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427918).length < 2 ^ (prefixWord ++ tailWord_6427918).sum := by decide
  have hdescent : baseEnd_6427918 < baseStart_6427918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427931 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 9]
def baseStart_6427931 : Nat := 118140960795 + 6427931 * 2 ^ 59
def prefixEnd_6427931 : Nat := 4983230072969 + 3 ^ 40 * 6427931 * 2
def baseEnd_6427931 : Nat := 1100206072311931808033663

theorem tailTrace_6427931 : CollatzResearch.WordTrace tailWord_6427931 prefixEnd_6427931 1100206072311931808033663 := by
  unfold tailWord_6427931
  simp only [CollatzResearch.WordTrace]
  refine ⟨234445904075711265059331647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156297269383807510039554431 234445904075711265059331647)
  ·
    refine ⟨351668856113566897588997471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234445904075711265059331647 351668856113566897588997471)
    ·
      refine ⟨527503284170350346383496207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351668856113566897588997471 527503284170350346383496207)
      ·
        refine ⟨791254926255525519575244311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527503284170350346383496207 791254926255525519575244311)
        ·
          refine ⟨1186882389383288279362866467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791254926255525519575244311 1186882389383288279362866467)
          ·
            refine ⟨1780323584074932419044299701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186882389383288279362866467 1780323584074932419044299701)
            ·
              refine ⟨166905336007024914285403097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1780323584074932419044299701 166905336007024914285403097)
              ·
                refine ⟨125179002005268685714052323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166905336007024914285403097 125179002005268685714052323)
                ·
                  refine ⟨187768503007903028571078485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125179002005268685714052323 187768503007903028571078485)
                  ·
                    refine ⟨1100206072311931808033663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187768503007903028571078485 1100206072311931808033663)
                    ·
                      rfl

theorem cell23_6427931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_6427931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427931 prefixEnd_6427931 := by exact prefixLift 6427931
  have htrace : WordTrace (prefixWord ++ tailWord_6427931) baseStart_6427931 baseEnd_6427931 := by
    simpa [prefixWord, tailWord_6427931, baseEnd_6427931] using wordTrace_append hprefix tailTrace_6427931
  have hstable : (prefixWord ++ tailWord_6427931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427931).length < 2 ^ (prefixWord ++ tailWord_6427931).sum := by decide
  have hdescent : baseEnd_6427931 < baseStart_6427931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427935 : List Nat := [1, 1, 2, 4, 5, 1, 9]
def baseStart_6427935 : Nat := 118140960795 + 6427935 * 2 ^ 59
def prefixEnd_6427935 : Nat := 4983230072969 + 3 ^ 40 * 6427935 * 2
def baseEnd_6427935 : Nat := 40748398405659424795691

theorem tailTrace_6427935 : CollatzResearch.WordTrace tailWord_6427935 prefixEnd_6427935 40748398405659424795691 := by
  unfold tailWord_6427935
  simp only [CollatzResearch.WordTrace]
  refine ⟨234446049967696773742477259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156297366645131182494984839 234446049967696773742477259)
  ·
    refine ⟨351669074951545160613715889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234446049967696773742477259 351669074951545160613715889)
    ·
      refine ⟨263751806213658870460286917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351669074951545160613715889 263751806213658870460286917)
      ·
        refine ⟨49453463665061038211303797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263751806213658870460286917 49453463665061038211303797)
        ·
          refine ⟨4636262218599472332309731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49453463665061038211303797 4636262218599472332309731)
          ·
            refine ⟨6954393327899208498464597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636262218599472332309731 6954393327899208498464597)
            ·
              refine ⟨40748398405659424795691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6954393327899208498464597 40748398405659424795691)
              ·
                rfl

theorem cell23_6427935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 9].length) (baseStart_6427935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427935 prefixEnd_6427935 := by exact prefixLift 6427935
  have htrace : WordTrace (prefixWord ++ tailWord_6427935) baseStart_6427935 baseEnd_6427935 := by
    simpa [prefixWord, tailWord_6427935, baseEnd_6427935] using wordTrace_append hprefix tailTrace_6427935
  have hstable : (prefixWord ++ tailWord_6427935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427935).length < 2 ^ (prefixWord ++ tailWord_6427935).sum := by decide
  have hdescent : baseEnd_6427935 < baseStart_6427935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427946 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6427946 : Nat := 118140960795 + 6427946 * 2 ^ 59
def prefixEnd_6427946 : Nat := 4983230072969 + 3 ^ 40 * 6427946 * 2
def baseEnd_6427946 : Nat := 3300625919145612865413421

theorem tailTrace_6427946 : CollatzResearch.WordTrace tailWord_6427946 prefixEnd_6427946 3300625919145612865413421 := by
  unfold tailWord_6427946
  simp only [CollatzResearch.WordTrace]
  refine ⟨58611612792664230655281923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156297634113771281747418461 58611612792664230655281923)
  ·
    refine ⟨87917419188996345982922885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58611612792664230655281923 87917419188996345982922885)
    ·
      refine ⟨16484516097936814871798041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87917419188996345982922885 16484516097936814871798041)
      ·
        refine ⟨12363387073452611153848531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16484516097936814871798041 12363387073452611153848531)
        ·
          refine ⟨18545080610178916730772797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12363387073452611153848531 18545080610178916730772797)
          ·
            refine ⟨6954405228817093774039799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18545080610178916730772797 6954405228817093774039799)
            ·
              refine ⟨10431607843225640661059699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954405228817093774039799 10431607843225640661059699)
              ·
                refine ⟨15647411764838460991589549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10431607843225640661059699 15647411764838460991589549)
                ·
                  refine ⟨5867779411814422871846081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15647411764838460991589549 5867779411814422871846081)
                  ·
                    refine ⟨4400834558860817153884561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5867779411814422871846081 4400834558860817153884561)
                    ·
                      refine ⟨3300625919145612865413421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400834558860817153884561 3300625919145612865413421)
                      ·
                        rfl

theorem cell23_6427946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6427946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427946 prefixEnd_6427946 := by exact prefixLift 6427946
  have htrace : WordTrace (prefixWord ++ tailWord_6427946) baseStart_6427946 baseEnd_6427946 := by
    simpa [prefixWord, tailWord_6427946, baseEnd_6427946] using wordTrace_append hprefix tailTrace_6427946
  have hstable : (prefixWord ++ tailWord_6427946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427946).length < 2 ^ (prefixWord ++ tailWord_6427946).sum := by decide
  have hdescent : baseEnd_6427946 < baseStart_6427946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6427962 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_6427962 : Nat := 118140960795 + 6427962 * 2 ^ 59
def prefixEnd_6427962 : Nat := 4983230072969 + 3 ^ 40 * 6427962 * 2
def baseEnd_6427962 : Nat := 3300634134836084802813347

theorem tailTrace_6427962 : CollatzResearch.WordTrace tailWord_6427962 prefixEnd_6427962 3300634134836084802813347 := by
  unfold tailWord_6427962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58611758684649739338427535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156298023159065971569140093 58611758684649739338427535)
  ·
    refine ⟨87917638026974609007641303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58611758684649739338427535 87917638026974609007641303)
    ·
      refine ⟨131876457040461913511461955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87917638026974609007641303 131876457040461913511461955)
      ·
        refine ⟨197814685560692870267192933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131876457040461913511461955 197814685560692870267192933)
        ·
          refine ⟨37090253542629913175098675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197814685560692870267192933 37090253542629913175098675)
          ·
            refine ⟨55635380313944869762648013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37090253542629913175098675 55635380313944869762648013)
            ·
              refine ⟨20863267617729326160993005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55635380313944869762648013 20863267617729326160993005)
              ·
                refine ⟨7823725356648497310372377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20863267617729326160993005 7823725356648497310372377)
                ·
                  refine ⟨5867794017486372982779283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823725356648497310372377 5867794017486372982779283)
                  ·
                    refine ⟨8801691026229559474168925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5867794017486372982779283 8801691026229559474168925)
                    ·
                      refine ⟨3300634134836084802813347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801691026229559474168925 3300634134836084802813347)
                      ·
                        rfl

theorem cell23_6427962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_6427962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6427962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6427962 prefixEnd_6427962 := by exact prefixLift 6427962
  have htrace : WordTrace (prefixWord ++ tailWord_6427962) baseStart_6427962 baseEnd_6427962 := by
    simpa [prefixWord, tailWord_6427962, baseEnd_6427962] using wordTrace_append hprefix tailTrace_6427962
  have hstable : (prefixWord ++ tailWord_6427962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6427962).length < 2 ^ (prefixWord ++ tailWord_6427962).sum := by decide
  have hdescent : baseEnd_6427962 < baseStart_6427962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6427962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428002 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6428002 : Nat := 118140960795 + 6428002 * 2 ^ 59
def prefixEnd_6428002 : Nat := 4983230072969 + 3 ^ 40 * 6428002 * 2
def baseEnd_6428002 : Nat := 3300654674062264646313163

theorem tailTrace_6428002 : CollatzResearch.WordTrace tailWord_6428002 prefixEnd_6428002 3300654674062264646313163 := by
  unfold tailWord_6428002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58612123414613511046291565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156298995772302696123444173 58612123414613511046291565)
  ·
    refine ⟨21979546280480066642359337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58612123414613511046291565 21979546280480066642359337)
    ·
      refine ⟨16484659710360049981769503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21979546280480066642359337 16484659710360049981769503)
      ·
        refine ⟨24726989565540074972654255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16484659710360049981769503 24726989565540074972654255)
        ·
          refine ⟨37090484348310112458981383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24726989565540074972654255 37090484348310112458981383)
          ·
            refine ⟨55635726522465168688472075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37090484348310112458981383 55635726522465168688472075)
            ·
              refine ⟨83453589783697753032708113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55635726522465168688472075 83453589783697753032708113)
              ·
                refine ⟨62590192337773314774531085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83453589783697753032708113 62590192337773314774531085)
                ·
                  refine ⟨23471322126664993040449157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62590192337773314774531085 23471322126664993040449157)
                  ·
                    refine ⟨4400872898749686195084217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23471322126664993040449157 4400872898749686195084217)
                    ·
                      refine ⟨3300654674062264646313163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400872898749686195084217 3300654674062264646313163)
                      ·
                        rfl

theorem cell23_6428002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6428002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428002 prefixEnd_6428002 := by exact prefixLift 6428002
  have htrace : WordTrace (prefixWord ++ tailWord_6428002) baseStart_6428002 baseEnd_6428002 := by
    simpa [prefixWord, tailWord_6428002, baseEnd_6428002] using wordTrace_append hprefix tailTrace_6428002
  have hstable : (prefixWord ++ tailWord_6428002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428002).length < 2 ^ (prefixWord ++ tailWord_6428002).sum := by decide
  have hdescent : baseEnd_6428002 < baseStart_6428002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428052 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6428052 : Nat := 118140960795 + 6428052 * 2 ^ 59
def prefixEnd_6428052 : Nat := 4983230072969 + 3 ^ 40 * 6428052 * 2
def baseEnd_6428052 : Nat := 3300680348094989450687933

theorem tailTrace_6428052 : CollatzResearch.WordTrace tailWord_6428052 prefixEnd_6428052 3300680348094989450687933 := by
  unfold tailWord_6428052
  simp only [CollatzResearch.WordTrace]
  refine ⟨117225158654136451362243205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156300211538848601816324273 117225158654136451362243205)
  ·
    refine ⟨21979717247650584630420601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117225158654136451362243205 21979717247650584630420601)
    ·
      refine ⟨16484787935737938472815451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21979717247650584630420601 16484787935737938472815451)
      ·
        refine ⟨24727181903606907709223177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16484787935737938472815451 24727181903606907709223177)
        ·
          refine ⟨18545386427705180781917383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24727181903606907709223177 18545386427705180781917383)
          ·
            refine ⟨27818079641557771172876075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18545386427705180781917383 27818079641557771172876075)
            ·
              refine ⟨41727119462336656759314113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27818079641557771172876075 41727119462336656759314113)
              ·
                refine ⟨31295339596752492569485585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41727119462336656759314113 31295339596752492569485585)
                ·
                  refine ⟨23471504697564369427114189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31295339596752492569485585 23471504697564369427114189)
                  ·
                    refine ⟨8801814261586638535167821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23471504697564369427114189 8801814261586638535167821)
                    ·
                      refine ⟨3300680348094989450687933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801814261586638535167821 3300680348094989450687933)
                      ·
                        rfl

theorem cell23_6428052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6428052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428052 prefixEnd_6428052 := by exact prefixLift 6428052
  have htrace : WordTrace (prefixWord ++ tailWord_6428052) baseStart_6428052 baseEnd_6428052 := by
    simpa [prefixWord, tailWord_6428052, baseEnd_6428052] using wordTrace_append hprefix tailTrace_6428052
  have hstable : (prefixWord ++ tailWord_6428052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428052).length < 2 ^ (prefixWord ++ tailWord_6428052).sum := by decide
  have hdescent : baseEnd_6428052 < baseStart_6428052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428075 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 6, 2]
def baseStart_6428075 : Nat := 118140960795 + 6428075 * 2 ^ 59
def prefixEnd_6428075 : Nat := 4983230072969 + 3 ^ 40 * 6428075 * 2
def baseEnd_6428075 : Nat := 3300692158150042860700327

theorem tailTrace_6428075 : CollatzResearch.WordTrace tailWord_6428075 prefixEnd_6428075 3300692158150042860700327 := by
  unfold tailWord_6428075
  simp only [CollatzResearch.WordTrace]
  refine ⟨234451156187189577652573679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156300770791459718435049119 234451156187189577652573679)
  ·
    refine ⟨351676734280784366478860519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234451156187189577652573679 351676734280784366478860519)
    ·
      refine ⟨527515101421176549718290779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351676734280784366478860519 527515101421176549718290779)
      ·
        refine ⟨791272652131764824577436169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527515101421176549718290779 791272652131764824577436169)
        ·
          refine ⟨593454489098823618433077127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791272652131764824577436169 593454489098823618433077127)
          ·
            refine ⟨890181733648235427649615691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593454489098823618433077127 890181733648235427649615691)
            ·
              refine ⟨1335272600472353141474423537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890181733648235427649615691 1335272600472353141474423537)
              ·
                refine ⟨1001454450354264856105817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335272600472353141474423537 1001454450354264856105817653)
                ·
                  refine ⟨93886354720712330259920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001454450354264856105817653 93886354720712330259920405)
                  ·
                    refine ⟨4400922877533390480933769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93886354720712330259920405 4400922877533390480933769)
                    ·
                      refine ⟨3300692158150042860700327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4400922877533390480933769 3300692158150042860700327)
                      ·
                        rfl

theorem cell23_6428075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6, 2].length) (baseStart_6428075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428075 prefixEnd_6428075 := by exact prefixLift 6428075
  have htrace : WordTrace (prefixWord ++ tailWord_6428075) baseStart_6428075 baseEnd_6428075 := by
    simpa [prefixWord, tailWord_6428075, baseEnd_6428075] using wordTrace_append hprefix tailTrace_6428075
  have hstable : (prefixWord ++ tailWord_6428075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428075).length < 2 ^ (prefixWord ++ tailWord_6428075).sum := by decide
  have hdescent : baseEnd_6428075 < baseStart_6428075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428095 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_6428095 : Nat := 118140960795 + 6428095 * 2 ^ 59
def prefixEnd_6428095 : Nat := 4983230072969 + 3 ^ 40 * 6428095 * 2
def baseEnd_6428095 : Nat := 3300702427763132782450235

theorem tailTrace_6428095 : CollatzResearch.WordTrace tailWord_6428095 prefixEnd_6428095 3300702427763132782450235 := by
  unfold tailWord_6428095
  simp only [CollatzResearch.WordTrace]
  refine ⟨234451885647117121068301739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156301257098078080712201159 234451885647117121068301739)
  ·
    refine ⟨351677828470675681602452609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234451885647117121068301739 351677828470675681602452609)
    ·
      refine ⟨263758371353006761201839457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351677828470675681602452609 263758371353006761201839457)
      ·
        refine ⟨197818778514755070901379593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263758371353006761201839457 197818778514755070901379593)
        ·
          refine ⟨148364083886066303176034695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197818778514755070901379593 148364083886066303176034695)
          ·
            refine ⟨222546125829099454764052043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148364083886066303176034695 222546125829099454764052043)
            ·
              refine ⟨333819188743649182146078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222546125829099454764052043 333819188743649182146078065)
              ·
                refine ⟨250364391557736886609558549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333819188743649182146078065 250364391557736886609558549)
                ·
                  refine ⟨11735830854268916559823057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250364391557736886609558549 11735830854268916559823057)
                  ·
                    refine ⟨8801873140701687419867293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11735830854268916559823057 8801873140701687419867293)
                    ·
                      refine ⟨3300702427763132782450235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801873140701687419867293 3300702427763132782450235)
                      ·
                        rfl

theorem cell23_6428095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_6428095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428095 prefixEnd_6428095 := by exact prefixLift 6428095
  have htrace : WordTrace (prefixWord ++ tailWord_6428095) baseStart_6428095 baseEnd_6428095 := by
    simpa [prefixWord, tailWord_6428095, baseEnd_6428095] using wordTrace_append hprefix tailTrace_6428095
  have hstable : (prefixWord ++ tailWord_6428095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428095).length < 2 ^ (prefixWord ++ tailWord_6428095).sum := by decide
  have hdescent : baseEnd_6428095 < baseStart_6428095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428185 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_6428185 : Nat := 118140960795 + 6428185 * 2 ^ 59
def prefixEnd_6428185 : Nat := 4983230072969 + 3 ^ 40 * 6428185 * 2
def baseEnd_6428185 : Nat := 3300748641022037430324821

theorem tailTrace_6428185 : CollatzResearch.WordTrace tailWord_6428185 prefixEnd_6428185 3300748641022037430324821 := by
  unfold tailWord_6428185
  simp only [CollatzResearch.WordTrace]
  refine ⟨234455168216791066439078009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156303445477860710959385339 234455168216791066439078009)
  ·
    refine ⟨175841376162593299829308507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234455168216791066439078009 175841376162593299829308507)
    ·
      refine ⟨263762064243889949743962761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175841376162593299829308507 263762064243889949743962761)
      ·
        refine ⟨197821548182917462307972071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263762064243889949743962761 197821548182917462307972071)
        ·
          refine ⟨296732322274376193461958107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197821548182917462307972071 296732322274376193461958107)
          ·
            refine ⟨445098483411564290192937161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296732322274376193461958107 445098483411564290192937161)
            ·
              refine ⟨333823862558673217644702871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445098483411564290192937161 333823862558673217644702871)
              ·
                refine ⟨500735793838009826467054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333823862558673217644702871 500735793838009826467054307)
                ·
                  refine ⟨751103690757014739700581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500735793838009826467054307 751103690757014739700581461)
                  ·
                    refine ⟨8801996376058766480866189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 751103690757014739700581461 8801996376058766480866189)
                    ·
                      refine ⟨3300748641022037430324821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8801996376058766480866189 3300748641022037430324821)
                      ·
                        rfl

theorem cell23_6428185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_6428185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428185 prefixEnd_6428185 := by exact prefixLift 6428185
  have htrace : WordTrace (prefixWord ++ tailWord_6428185) baseStart_6428185 baseEnd_6428185 := by
    simpa [prefixWord, tailWord_6428185, baseEnd_6428185] using wordTrace_append hprefix tailTrace_6428185
  have hstable : (prefixWord ++ tailWord_6428185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428185).length < 2 ^ (prefixWord ++ tailWord_6428185).sum := by decide
  have hdescent : baseEnd_6428185 < baseStart_6428185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428192 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_6428192 : Nat := 118140960795 + 6428192 * 2 ^ 59
def prefixEnd_6428192 : Nat := 4983230072969 + 3 ^ 40 * 6428192 * 2
def baseEnd_6428192 : Nat := 1100250745128872967645763

theorem tailTrace_6428192 : CollatzResearch.WordTrace tailWord_6428192 prefixEnd_6428192 1100250745128872967645763 := by
  unfold tailWord_6428192
  simp only [CollatzResearch.WordTrace]
  refine ⟨117227711763882853317291415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156303615685177137756388553 117227711763882853317291415)
  ·
    refine ⟨175841567645824279975937123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117227711763882853317291415 175841567645824279975937123)
    ·
      refine ⟨263762351468736419963905685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175841567645824279975937123 263762351468736419963905685)
      ·
        refine ⟨12363860225097019685808079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 263762351468736419963905685 12363860225097019685808079)
        ·
          refine ⟨18545790337645529528712119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12363860225097019685808079 18545790337645529528712119)
          ·
            refine ⟨27818685506468294293068179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18545790337645529528712119 27818685506468294293068179)
            ·
              refine ⟨41728028259702441439602269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27818685506468294293068179 41728028259702441439602269)
              ·
                refine ⟨15648010597388415539850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41728028259702441439602269 15648010597388415539850851)
                ·
                  refine ⟨23472015896082623309776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15648010597388415539850851 23472015896082623309776277)
                  ·
                    refine ⟨1100250745128872967645763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23472015896082623309776277 1100250745128872967645763)
                    ·
                      rfl

theorem cell23_6428192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_6428192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428192 prefixEnd_6428192 := by exact prefixLift 6428192
  have htrace : WordTrace (prefixWord ++ tailWord_6428192) baseStart_6428192 baseEnd_6428192 := by
    simpa [prefixWord, tailWord_6428192, baseEnd_6428192] using wordTrace_append hprefix tailTrace_6428192
  have hstable : (prefixWord ++ tailWord_6428192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428192).length < 2 ^ (prefixWord ++ tailWord_6428192).sum := by decide
  have hdescent : baseEnd_6428192 < baseStart_6428192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428216 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_6428216 : Nat := 118140960795 + 6428216 * 2 ^ 59
def prefixEnd_6428216 : Nat := 4983230072969 + 3 ^ 40 * 6428216 * 2
def baseEnd_6428216 : Nat := 3300764558922326809037179

theorem tailTrace_6428216 : CollatzResearch.WordTrace tailWord_6428216 prefixEnd_6428216 3300764558922326809037179 := by
  unfold tailWord_6428216
  simp only [CollatzResearch.WordTrace]
  refine ⟨117228149439839379366728251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156304199253119172488971001 117228149439839379366728251)
  ·
    refine ⟨175842224159759069050092377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117228149439839379366728251 175842224159759069050092377)
    ·
      refine ⟨131881668119819301787569283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175842224159759069050092377 131881668119819301787569283)
      ·
        refine ⟨197822502179728952681353925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131881668119819301787569283 197822502179728952681353925)
        ·
          refine ⟨37091719158699178627753861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197822502179728952681353925 37091719158699178627753861)
          ·
            refine ⟨6954697342256095992703849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37091719158699178627753861 6954697342256095992703849)
            ·
              refine ⟨5216023006692071994527887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954697342256095992703849 5216023006692071994527887)
              ·
                refine ⟨7824034510038107991791831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216023006692071994527887 7824034510038107991791831)
                ·
                  refine ⟨11736051765057161987687747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7824034510038107991791831 11736051765057161987687747)
                  ·
                    refine ⟨17604077647585742981531621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11736051765057161987687747 17604077647585742981531621)
                    ·
                      refine ⟨3300764558922326809037179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17604077647585742981531621 3300764558922326809037179)
                      ·
                        rfl

theorem cell23_6428216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_6428216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428216 prefixEnd_6428216 := by exact prefixLift 6428216
  have htrace : WordTrace (prefixWord ++ tailWord_6428216) baseStart_6428216 baseEnd_6428216 := by
    simpa [prefixWord, tailWord_6428216, baseEnd_6428216] using wordTrace_append hprefix tailTrace_6428216
  have hstable : (prefixWord ++ tailWord_6428216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428216).length < 2 ^ (prefixWord ++ tailWord_6428216).sum := by decide
  have hdescent : baseEnd_6428216 < baseStart_6428216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428249 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_6428249 : Nat := 118140960795 + 6428249 * 2 ^ 59
def prefixEnd_6428249 : Nat := 4983230072969 + 3 ^ 40 * 6428249 * 2
def baseEnd_6428249 : Nat := 3300781503783925179924527

theorem tailTrace_6428249 : CollatzResearch.WordTrace tailWord_6428249 prefixEnd_6428249 3300781503783925179924527 := by
  unfold tailWord_6428249
  simp only [CollatzResearch.WordTrace]
  refine ⟨234457502488559205369407801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156305001659039470246271867 234457502488559205369407801)
  ·
    refine ⟨175843126866419404027055851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234457502488559205369407801 175843126866419404027055851)
    ·
      refine ⟨263764690299629106040583777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175843126866419404027055851 263764690299629106040583777)
      ·
        refine ⟨197823517724721829530437833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263764690299629106040583777 197823517724721829530437833)
        ·
          refine ⟨148367638293541372147828375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197823517724721829530437833 148367638293541372147828375)
          ·
            refine ⟨222551457440312058221742563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148367638293541372147828375 222551457440312058221742563)
            ·
              refine ⟨333827186160468087332613845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222551457440312058221742563 333827186160468087332613845)
              ·
                refine ⟨7824074675635970796858137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 333827186160468087332613845 7824074675635970796858137)
                ·
                  refine ⟨5868056006726978097643603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7824074675635970796858137 5868056006726978097643603)
                  ·
                    refine ⟨8802084010090467146465405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868056006726978097643603 8802084010090467146465405)
                    ·
                      refine ⟨3300781503783925179924527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802084010090467146465405 3300781503783925179924527)
                      ·
                        rfl

theorem cell23_6428249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_6428249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428249 prefixEnd_6428249 := by exact prefixLift 6428249
  have htrace : WordTrace (prefixWord ++ tailWord_6428249) baseStart_6428249 baseEnd_6428249 := by
    simpa [prefixWord, tailWord_6428249, baseEnd_6428249] using wordTrace_append hprefix tailTrace_6428249
  have hstable : (prefixWord ++ tailWord_6428249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428249).length < 2 ^ (prefixWord ++ tailWord_6428249).sum := by decide
  have hdescent : baseEnd_6428249 < baseStart_6428249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428265 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_6428265 : Nat := 118140960795 + 6428265 * 2 ^ 59
def prefixEnd_6428265 : Nat := 4983230072969 + 3 ^ 40 * 6428265 * 2
def baseEnd_6428265 : Nat := 1100263239824799039108151

theorem tailTrace_6428265 : CollatzResearch.WordTrace tailWord_6428265 prefixEnd_6428265 1100263239824799039108151 := by
  unfold tailWord_6428265
  simp only [CollatzResearch.WordTrace]
  refine ⟨234458086056501240101990249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156305390704334160067993499 234458086056501240101990249)
  ·
    refine ⟨175843564542375930076492687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234458086056501240101990249 175843564542375930076492687)
    ·
      refine ⟨263765346813563895114739031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175843564542375930076492687 263765346813563895114739031)
      ·
        refine ⟨395648020220345842672108547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263765346813563895114739031 395648020220345842672108547)
        ·
          refine ⟨593472030330518764008162821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395648020220345842672108547 593472030330518764008162821)
          ·
            refine ⟨111276005686972268251530529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593472030330518764008162821 111276005686972268251530529)
            ·
              refine ⟨83457004265229201188647897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111276005686972268251530529 83457004265229201188647897)
              ·
                refine ⟨62592753198921900891485923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83457004265229201188647897 62592753198921900891485923)
                ·
                  refine ⟨93889129798382851337228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62592753198921900891485923 93889129798382851337228885)
                  ·
                    refine ⟨1100263239824799039108151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93889129798382851337228885 1100263239824799039108151)
                    ·
                      rfl

theorem cell23_6428265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_6428265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428265 prefixEnd_6428265 := by exact prefixLift 6428265
  have htrace : WordTrace (prefixWord ++ tailWord_6428265) baseStart_6428265 baseEnd_6428265 := by
    simpa [prefixWord, tailWord_6428265, baseEnd_6428265] using wordTrace_append hprefix tailTrace_6428265
  have hstable : (prefixWord ++ tailWord_6428265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428265).length < 2 ^ (prefixWord ++ tailWord_6428265).sum := by decide
  have hdescent : baseEnd_6428265 < baseStart_6428265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428346 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_6428346 : Nat := 118140960795 + 6428346 * 2 ^ 59
def prefixEnd_6428346 : Nat := 4983230072969 + 3 ^ 40 * 6428346 * 2
def baseEnd_6428346 : Nat := 366759034600823477823509

theorem tailTrace_6428346 : CollatzResearch.WordTrace tailWord_6428346 prefixEnd_6428346 366759034600823477823509 := by
  unfold tailWord_6428346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58615260092301947733922223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156307360246138527290459261 58615260092301947733922223)
  ·
    refine ⟨87922890138452921600883335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58615260092301947733922223 87922890138452921600883335)
    ·
      refine ⟨131884335207679382401325003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87922890138452921600883335 131884335207679382401325003)
      ·
        refine ⟨197826502811519073601987505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131884335207679382401325003 197826502811519073601987505)
        ·
          refine ⟨148369877108639305201490629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197826502811519073601987505 148369877108639305201490629)
          ·
            refine ⟨27819351957869869725279493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148369877108639305201490629 27819351957869869725279493)
            ·
              refine ⟨5216128492100600573489905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27819351957869869725279493 5216128492100600573489905)
              ·
                refine ⟨3912096369075450430117429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216128492100600573489905 3912096369075450430117429)
                ·
                  refine ⟨366759034600823477823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912096369075450430117429 366759034600823477823509)
                  ·
                    rfl

theorem cell23_6428346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_6428346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428346 prefixEnd_6428346 := by exact prefixLift 6428346
  have htrace : WordTrace (prefixWord ++ tailWord_6428346) baseStart_6428346 baseEnd_6428346 := by
    simpa [prefixWord, tailWord_6428346, baseEnd_6428346] using wordTrace_append hprefix tailTrace_6428346
  have hstable : (prefixWord ++ tailWord_6428346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428346).length < 2 ^ (prefixWord ++ tailWord_6428346).sum := by decide
  have hdescent : baseEnd_6428346 < baseStart_6428346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428349 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_6428349 : Nat := 118140960795 + 6428349 * 2 ^ 59
def prefixEnd_6428349 : Nat := 4983230072969 + 3 ^ 40 * 6428349 * 2
def baseEnd_6428349 : Nat := 3300832851849374788674067

theorem tailTrace_6428349 : CollatzResearch.WordTrace tailWord_6428349 prefixEnd_6428349 3300832851849374788674067 := by
  unfold tailWord_6428349
  simp only [CollatzResearch.WordTrace]
  refine ⟨234461149788196922448048101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156307433192131281632032067 234461149788196922448048101)
  ·
    refine ⟨43961465585286922959009019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234461149788196922448048101 43961465585286922959009019)
    ·
      refine ⟨65942198377930384438513529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43961465585286922959009019 65942198377930384438513529)
      ·
        refine ⟨49456648783447788328885147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65942198377930384438513529 49456648783447788328885147)
        ·
          refine ⟨74184973175171682493327721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49456648783447788328885147 74184973175171682493327721)
          ·
            refine ⟨55638729881378761869995791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74184973175171682493327721 55638729881378761869995791)
            ·
              refine ⟨83458094822068142804993687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55638729881378761869995791 83458094822068142804993687)
              ·
                refine ⟨125187142233102214207490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83458094822068142804993687 125187142233102214207490531)
                ·
                  refine ⟨187780713349653321311235797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125187142233102214207490531 187780713349653321311235797)
                  ·
                    refine ⟨4401110469132499718232089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187780713349653321311235797 4401110469132499718232089)
                    ·
                      refine ⟨3300832851849374788674067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401110469132499718232089 3300832851849374788674067)
                      ·
                        rfl

theorem cell23_6428349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_6428349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428349 prefixEnd_6428349 := by exact prefixLift 6428349
  have htrace : WordTrace (prefixWord ++ tailWord_6428349) baseStart_6428349 baseEnd_6428349 := by
    simpa [prefixWord, tailWord_6428349, baseEnd_6428349] using wordTrace_append hprefix tailTrace_6428349
  have hstable : (prefixWord ++ tailWord_6428349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428349).length < 2 ^ (prefixWord ++ tailWord_6428349).sum := by decide
  have hdescent : baseEnd_6428349 < baseStart_6428349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428352 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_6428352 : Nat := 118140960795 + 6428352 * 2 ^ 59
def prefixEnd_6428352 : Nat := 4983230072969 + 3 ^ 40 * 6428352 * 2
def baseEnd_6428352 : Nat := 3300834392291338276936553

theorem tailTrace_6428352 : CollatzResearch.WordTrace tailWord_6428352 prefixEnd_6428352 3300834392291338276936553 := by
  unfold tailWord_6428352
  simp only [CollatzResearch.WordTrace]
  refine ⟨117230629603593026980203655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156307506138124035973604873 117230629603593026980203655)
  ·
    refine ⟨175845944405389540470305483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117230629603593026980203655 175845944405389540470305483)
    ·
      refine ⟨263768916608084310705458225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175845944405389540470305483 263768916608084310705458225)
      ·
        refine ⟨197826687456063233029093669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263768916608084310705458225 197826687456063233029093669)
        ·
          refine ⟨37092503898011856192955063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197826687456063233029093669 37092503898011856192955063)
          ·
            refine ⟨55638755847017784289432595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37092503898011856192955063 55638755847017784289432595)
            ·
              refine ⟨83458133770526676434148893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55638755847017784289432595 83458133770526676434148893)
              ·
                refine ⟨31296800163947503662805835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83458133770526676434148893 31296800163947503662805835)
                ·
                  refine ⟨46945200245921255494208753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31296800163947503662805835 46945200245921255494208753)
                  ·
                    refine ⟨35208900184440941620656565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46945200245921255494208753 35208900184440941620656565)
                    ·
                      refine ⟨3300834392291338276936553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35208900184440941620656565 3300834392291338276936553)
                      ·
                        rfl

theorem cell23_6428352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_6428352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428352 prefixEnd_6428352 := by exact prefixLift 6428352
  have htrace : WordTrace (prefixWord ++ tailWord_6428352) baseStart_6428352 baseEnd_6428352 := by
    simpa [prefixWord, tailWord_6428352, baseEnd_6428352] using wordTrace_append hprefix tailTrace_6428352
  have hstable : (prefixWord ++ tailWord_6428352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428352).length < 2 ^ (prefixWord ++ tailWord_6428352).sum := by decide
  have hdescent : baseEnd_6428352 < baseStart_6428352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428389 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_6428389 : Nat := 118140960795 + 6428389 * 2 ^ 59
def prefixEnd_6428389 : Nat := 4983230072969 + 3 ^ 40 * 6428389 * 2
def baseEnd_6428389 : Nat := 1100284463691851544057961

theorem tailTrace_6428389 : CollatzResearch.WordTrace tailWord_6428389 prefixEnd_6428389 1100284463691851544057961 := by
  unfold tailWord_6428389
  simp only [CollatzResearch.WordTrace]
  refine ⟨234462608708052009279504221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156308405805368006186336147 234462608708052009279504221)
  ·
    refine ⟨87923478265519503479814083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234462608708052009279504221 87923478265519503479814083)
    ·
      refine ⟨131885217398279255219721125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87923478265519503479814083 131885217398279255219721125)
      ·
        refine ⟨24728478262177360353697711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131885217398279255219721125 24728478262177360353697711)
        ·
          refine ⟨37092717393266040530546567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24728478262177360353697711 37092717393266040530546567)
          ·
            refine ⟨55639076089899060795819851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37092717393266040530546567 55639076089899060795819851)
            ·
              refine ⟨83458614134848591193729777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55639076089899060795819851 83458614134848591193729777)
              ·
                refine ⟨62593960601136443395297333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83458614134848591193729777 62593960601136443395297333)
                ·
                  refine ⟨5868183806356541568309125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62593960601136443395297333 5868183806356541568309125)
                  ·
                    refine ⟨1100284463691851544057961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868183806356541568309125 1100284463691851544057961)
                    ·
                      rfl

theorem cell23_6428389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_6428389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428389 prefixEnd_6428389 := by exact prefixLift 6428389
  have htrace : WordTrace (prefixWord ++ tailWord_6428389) baseStart_6428389 baseEnd_6428389 := by
    simpa [prefixWord, tailWord_6428389, baseEnd_6428389] using wordTrace_append hprefix tailTrace_6428389
  have hstable : (prefixWord ++ tailWord_6428389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428389).length < 2 ^ (prefixWord ++ tailWord_6428389).sum := by decide
  have hdescent : baseEnd_6428389 < baseStart_6428389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428399 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_6428399 : Nat := 118140960795 + 6428399 * 2 ^ 59
def prefixEnd_6428399 : Nat := 4983230072969 + 3 ^ 40 * 6428399 * 2
def baseEnd_6428399 : Nat := 3300858525882099593048837

theorem tailTrace_6428399 : CollatzResearch.WordTrace tailWord_6428399 prefixEnd_6428399 3300858525882099593048837 := by
  unfold tailWord_6428399
  simp only [CollatzResearch.WordTrace]
  refine ⟨234462973438015780987368251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156308648958677187324912167 234462973438015780987368251)
  ·
    refine ⟨351694460157023671481052377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234462973438015780987368251 351694460157023671481052377)
    ·
      refine ⟨263770845117767753610789283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351694460157023671481052377 263770845117767753610789283)
      ·
        refine ⟨395656267676651630416183925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263770845117767753610789283 395656267676651630416183925)
        ·
          refine ⟨37092775094686090351517243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395656267676651630416183925 37092775094686090351517243)
          ·
            refine ⟨55639162642029135527275865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37092775094686090351517243 55639162642029135527275865)
            ·
              refine ⟨41729371981521851645456899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55639162642029135527275865 41729371981521851645456899)
              ·
                refine ⟨62594057972282777468185349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41729371981521851645456899 62594057972282777468185349)
                ·
                  refine ⟨11736385869803020775284753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62594057972282777468185349 11736385869803020775284753)
                  ·
                    refine ⟨8802289402352265581463565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11736385869803020775284753 8802289402352265581463565)
                    ·
                      refine ⟨3300858525882099593048837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802289402352265581463565 3300858525882099593048837)
                      ·
                        rfl

theorem cell23_6428399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_6428399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428399 prefixEnd_6428399 := by exact prefixLift 6428399
  have htrace : WordTrace (prefixWord ++ tailWord_6428399) baseStart_6428399 baseEnd_6428399 := by
    simpa [prefixWord, tailWord_6428399, baseEnd_6428399] using wordTrace_append hprefix tailTrace_6428399
  have hstable : (prefixWord ++ tailWord_6428399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428399).length < 2 ^ (prefixWord ++ tailWord_6428399).sum := by decide
  have hdescent : baseEnd_6428399 < baseStart_6428399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428406 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_6428406 : Nat := 118140960795 + 6428406 * 2 ^ 59
def prefixEnd_6428406 : Nat := 4983230072969 + 3 ^ 40 * 6428406 * 2
def baseEnd_6428406 : Nat := 1100287373415560355220435

theorem tailTrace_6428406 : CollatzResearch.WordTrace tailWord_6428406 prefixEnd_6428406 1100287373415560355220435 := by
  unfold tailWord_6428406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653951796811901323929567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156308819165993614121915381 14653951796811901323929567)
  ·
    refine ⟨21980927695217851985894351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653951796811901323929567 21980927695217851985894351)
    ·
      refine ⟨32971391542826777978841527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21980927695217851985894351 32971391542826777978841527)
      ·
        refine ⟨49457087314240166968262291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32971391542826777978841527 49457087314240166968262291)
        ·
          refine ⟨74185630971360250452393437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49457087314240166968262291 74185630971360250452393437)
          ·
            refine ⟨27819611614260093919647539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74185630971360250452393437 27819611614260093919647539)
            ·
              refine ⟨41729417421390140879471309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27819611614260093919647539 41729417421390140879471309)
              ·
                refine ⟨15648531533021302829801741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41729417421390140879471309 15648531533021302829801741)
                ·
                  refine ⟨5868199324882988561175653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15648531533021302829801741 5868199324882988561175653)
                  ·
                    refine ⟨1100287373415560355220435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868199324882988561175653 1100287373415560355220435)
                    ·
                      rfl

theorem cell23_6428406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_6428406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428406 prefixEnd_6428406 := by exact prefixLift 6428406
  have htrace : WordTrace (prefixWord ++ tailWord_6428406) baseStart_6428406 baseEnd_6428406 := by
    simpa [prefixWord, tailWord_6428406, baseEnd_6428406] using wordTrace_append hprefix tailTrace_6428406
  have hstable : (prefixWord ++ tailWord_6428406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428406).length < 2 ^ (prefixWord ++ tailWord_6428406).sum := by decide
  have hdescent : baseEnd_6428406 < baseStart_6428406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428470 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6428470 : Nat := 118140960795 + 6428470 * 2 ^ 59
def prefixEnd_6428470 : Nat := 4983230072969 + 3 ^ 40 * 6428470 * 2
def baseEnd_6428470 : Nat := 366766109223174312806779

theorem tailTrace_6428470 : CollatzResearch.WordTrace tailWord_6428470 prefixEnd_6428470 366766109223174312806779 := by
  unfold tailWord_6428470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654097688797410007075179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156310375347172373408801909 14654097688797410007075179)
  ·
    refine ⟨21981146533196115010612769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654097688797410007075179 21981146533196115010612769)
    ·
      refine ⟨16485859899897086257959577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21981146533196115010612769 16485859899897086257959577)
      ·
        refine ⟨12364394924922814693469683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16485859899897086257959577 12364394924922814693469683)
        ·
          refine ⟨18546592387384222040204525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364394924922814693469683 18546592387384222040204525)
          ·
            refine ⟨6954972145269083265076697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18546592387384222040204525 6954972145269083265076697)
            ·
              refine ⟨5216229108951812448807523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954972145269083265076697 5216229108951812448807523)
              ·
                refine ⟨7824343663427718673211285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216229108951812448807523 7824343663427718673211285)
                ·
                  refine ⟨366766109223174312806779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7824343663427718673211285 366766109223174312806779)
                  ·
                    rfl

theorem cell23_6428470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6428470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428470 prefixEnd_6428470 := by exact prefixLift 6428470
  have htrace : WordTrace (prefixWord ++ tailWord_6428470) baseStart_6428470 baseEnd_6428470 := by
    simpa [prefixWord, tailWord_6428470, baseEnd_6428470] using wordTrace_append hprefix tailTrace_6428470
  have hstable : (prefixWord ++ tailWord_6428470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428470).length < 2 ^ (prefixWord ++ tailWord_6428470).sum := by decide
  have hdescent : baseEnd_6428470 < baseStart_6428470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428514 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6428514 : Nat := 118140960795 + 6428514 * 2 ^ 59
def prefixEnd_6428514 : Nat := 4983230072969 + 3 ^ 40 * 6428514 * 2
def baseEnd_6428514 : Nat := 3300917576157366643110809

theorem tailTrace_6428514 : CollatzResearch.WordTrace tailWord_6428514 prefixEnd_6428514 3300917576157366643110809 := by
  unfold tailWord_6428514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58616791958149788906951149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156311445221732770418536397 58616791958149788906951149)
  ·
    refine ⟨21981296984306170840106681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58616791958149788906951149 21981296984306170840106681)
    ·
      refine ⟨16485972738229628130080011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21981296984306170840106681 16485972738229628130080011)
      ·
        refine ⟨24728959107344442195120017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16485972738229628130080011 24728959107344442195120017)
        ·
          refine ⟨18546719330508331646340013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24728959107344442195120017 18546719330508331646340013)
          ·
            refine ⟨6955019748940624367377505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18546719330508331646340013 6955019748940624367377505)
            ·
              refine ⟨5216264811705468275533129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955019748940624367377505 5216264811705468275533129)
              ·
                refine ⟨3912198608779101206649847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216264811705468275533129 3912198608779101206649847)
                ·
                  refine ⟨5868297913168651809974771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912198608779101206649847 5868297913168651809974771)
                  ·
                    refine ⟨8802446869752977714962157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868297913168651809974771 8802446869752977714962157)
                    ·
                      refine ⟨3300917576157366643110809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802446869752977714962157 3300917576157366643110809)
                      ·
                        rfl

theorem cell23_6428514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6428514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428514 prefixEnd_6428514 := by exact prefixLift 6428514
  have htrace : WordTrace (prefixWord ++ tailWord_6428514) baseStart_6428514 baseEnd_6428514 := by
    simpa [prefixWord, tailWord_6428514, baseEnd_6428514] using wordTrace_append hprefix tailTrace_6428514
  have hstable : (prefixWord ++ tailWord_6428514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428514).length < 2 ^ (prefixWord ++ tailWord_6428514).sum := by decide
  have hdescent : baseEnd_6428514 < baseStart_6428514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428526 : List Nat := [4, 1, 2, 3, 1, 1, 3, 8]
def baseStart_6428526 : Nat := 118140960795 + 6428526 * 2 ^ 59
def prefixEnd_6428526 : Nat := 4983230072969 + 3 ^ 40 * 6428526 * 2
def baseEnd_6428526 : Nat := 122256434737971133191139

theorem tailTrace_6428526 : CollatzResearch.WordTrace tailWord_6428526 prefixEnd_6428526 122256434737971133191139 := by
  unfold tailWord_6428526
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308450688569460209655179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156311737005703787784827621 29308450688569460209655179)
  ·
    refine ⟨43962676032854190314482769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29308450688569460209655179 43962676032854190314482769)
    ·
      refine ⟨32972007024640642735862077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43962676032854190314482769 32972007024640642735862077)
      ·
        refine ⟨12364502634240241025948279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32972007024640642735862077 12364502634240241025948279)
        ·
          refine ⟨18546753951360361538922419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364502634240241025948279 18546753951360361538922419)
          ·
            refine ⟨27820130927040542308383629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18546753951360361538922419 27820130927040542308383629)
            ·
              refine ⟨10432549097640203365643861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27820130927040542308383629 10432549097640203365643861)
              ·
                refine ⟨122256434737971133191139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10432549097640203365643861 122256434737971133191139)
                ·
                  rfl

theorem cell23_6428526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_6428526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428526 prefixEnd_6428526 := by exact prefixLift 6428526
  have htrace : WordTrace (prefixWord ++ tailWord_6428526) baseStart_6428526 baseEnd_6428526 := by
    simpa [prefixWord, tailWord_6428526, baseEnd_6428526] using wordTrace_append hprefix tailTrace_6428526
  have hstable : (prefixWord ++ tailWord_6428526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428526).length < 2 ^ (prefixWord ++ tailWord_6428526).sum := by decide
  have hdescent : baseEnd_6428526 < baseStart_6428526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428549 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_6428549 : Nat := 118140960795 + 6428549 * 2 ^ 59
def prefixEnd_6428549 : Nat := 4983230072969 + 3 ^ 40 * 6428549 * 2
def baseEnd_6428549 : Nat := 3300935547980274006173147

theorem tailTrace_6428549 : CollatzResearch.WordTrace tailWord_6428549 prefixEnd_6428549 3300935547980274006173147 := by
  unfold tailWord_6428549
  simp only [CollatzResearch.WordTrace]
  refine ⟨234468444387472356605328701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156312296258314904403552467 234468444387472356605328701)
  ·
    refine ⟨87925666645302133726998263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234468444387472356605328701 87925666645302133726998263)
    ·
      refine ⟨131888499967953200590497395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87925666645302133726998263 131888499967953200590497395)
      ·
        refine ⟨197832749951929800885746093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131888499967953200590497395 197832749951929800885746093)
        ·
          refine ⟨74187281231973675332154785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197832749951929800885746093 74187281231973675332154785)
          ·
            refine ⟨55640460923980256499116089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74187281231973675332154785 55640460923980256499116089)
            ·
              refine ⟨41730345692985192374337067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55640460923980256499116089 41730345692985192374337067)
              ·
                refine ⟨62595518539477788561505601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41730345692985192374337067 62595518539477788561505601)
                ·
                  refine ⟨46946638904608341421129201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62595518539477788561505601 46946638904608341421129201)
                  ·
                    refine ⟨35209979178456256065846901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46946638904608341421129201 35209979178456256065846901)
                    ·
                      refine ⟨3300935547980274006173147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35209979178456256065846901 3300935547980274006173147)
                      ·
                        rfl

theorem cell23_6428549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_6428549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428549 prefixEnd_6428549 := by exact prefixLift 6428549
  have htrace : WordTrace (prefixWord ++ tailWord_6428549) baseStart_6428549 baseEnd_6428549 := by
    simpa [prefixWord, tailWord_6428549, baseEnd_6428549] using wordTrace_append hprefix tailTrace_6428549
  have hstable : (prefixWord ++ tailWord_6428549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428549).length < 2 ^ (prefixWord ++ tailWord_6428549).sum := by decide
  have hdescent : baseEnd_6428549 < baseStart_6428549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428554 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6428554 : Nat := 118140960795 + 6428554 * 2 ^ 59
def prefixEnd_6428554 : Nat := 4983230072969 + 3 ^ 40 * 6428554 * 2
def baseEnd_6428554 : Nat := 3300938115383546486610625

theorem tailTrace_6428554 : CollatzResearch.WordTrace tailWord_6428554 prefixEnd_6428554 3300938115383546486610625 := by
  unfold tailWord_6428554
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617156688113560614815179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156312417834969494972840477 58617156688113560614815179)
  ·
    refine ⟨87925735032170340922222769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58617156688113560614815179 87925735032170340922222769)
    ·
      refine ⟨65944301274127755691667077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87925735032170340922222769 65944301274127755691667077)
      ·
        refine ⟨12364556488898954192187577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65944301274127755691667077 12364556488898954192187577)
        ·
          refine ⟨9273417366674215644140683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12364556488898954192187577 9273417366674215644140683)
          ·
            refine ⟨13910126050011323466211025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273417366674215644140683 13910126050011323466211025)
            ·
              refine ⟨10432594537508492599658269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13910126050011323466211025 10432594537508492599658269)
              ·
                refine ⟨3912222951565684724871851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10432594537508492599658269 3912222951565684724871851)
                ·
                  refine ⟨5868334427348527087307777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912222951565684724871851 5868334427348527087307777)
                  ·
                    refine ⟨4401250820511395315480833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868334427348527087307777 4401250820511395315480833)
                    ·
                      refine ⟨3300938115383546486610625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401250820511395315480833 3300938115383546486610625)
                      ·
                        rfl

theorem cell23_6428554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6428554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428554 prefixEnd_6428554 := by exact prefixLift 6428554
  have htrace : WordTrace (prefixWord ++ tailWord_6428554) baseStart_6428554 baseEnd_6428554 := by
    simpa [prefixWord, tailWord_6428554, baseEnd_6428554] using wordTrace_append hprefix tailTrace_6428554
  have hstable : (prefixWord ++ tailWord_6428554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428554).length < 2 ^ (prefixWord ++ tailWord_6428554).sum := by decide
  have hdescent : baseEnd_6428554 < baseStart_6428554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428569 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_6428569 : Nat := 118140960795 + 6428569 * 2 ^ 59
def prefixEnd_6428569 : Nat := 4983230072969 + 3 ^ 40 * 6428569 * 2
def baseEnd_6428569 : Nat := 1100315272531121309307685

theorem tailTrace_6428569 : CollatzResearch.WordTrace tailWord_6428569 prefixEnd_6428569 1100315272531121309307685 := by
  unfold tailWord_6428569
  simp only [CollatzResearch.WordTrace]
  refine ⟨234469173847399900021056761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156312782564933266680704507 234469173847399900021056761)
  ·
    refine ⟨175851880385549925015792571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234469173847399900021056761 175851880385549925015792571)
    ·
      refine ⟨263777820578324887523688857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175851880385549925015792571 263777820578324887523688857)
      ·
        refine ⟨197833365433743665642766643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263777820578324887523688857 197833365433743665642766643)
        ·
          refine ⟨296750048150615498464149965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197833365433743665642766643 296750048150615498464149965)
          ·
            refine ⟨111281268056480811924056237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296750048150615498464149965 111281268056480811924056237)
            ·
              refine ⟨41730475521180304471521089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111281268056480811924056237 41730475521180304471521089)
              ·
                refine ⟨31297856640885228353640817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41730475521180304471521089 31297856640885228353640817)
                ·
                  refine ⟨23473392480663921265230613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31297856640885228353640817 23473392480663921265230613)
                  ·
                    refine ⟨1100315272531121309307685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23473392480663921265230613 1100315272531121309307685)
                    ·
                      rfl

theorem cell23_6428569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_6428569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428569 prefixEnd_6428569 := by exact prefixLift 6428569
  have htrace : WordTrace (prefixWord ++ tailWord_6428569) baseStart_6428569 baseEnd_6428569 := by
    simpa [prefixWord, tailWord_6428569, baseEnd_6428569] using wordTrace_append hprefix tailTrace_6428569
  have hstable : (prefixWord ++ tailWord_6428569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428569).length < 2 ^ (prefixWord ++ tailWord_6428569).sum := by decide
  have hdescent : baseEnd_6428569 < baseStart_6428569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428570 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6428570 : Nat := 118140960795 + 6428570 * 2 ^ 59
def prefixEnd_6428570 : Nat := 4983230072969 + 3 ^ 40 * 6428570 * 2
def baseEnd_6428570 : Nat := 3300946331074018424010551

theorem tailTrace_6428570 : CollatzResearch.WordTrace tailWord_6428570 prefixEnd_6428570 3300946331074018424010551 := by
  unfold tailWord_6428570
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617302580099069297960791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156312806880264184794562109 58617302580099069297960791)
  ·
    refine ⟨87925953870148603946941187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58617302580099069297960791 87925953870148603946941187)
    ·
      refine ⟨131888930805222905920411781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87925953870148603946941187 131888930805222905920411781)
      ·
        refine ⟨24729174525979294860077209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131888930805222905920411781 24729174525979294860077209)
        ·
          refine ⟨18546880894484471145057907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24729174525979294860077209 18546880894484471145057907)
          ·
            refine ⟨27820321341726706717586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18546880894484471145057907 27820321341726706717586861)
            ·
              refine ⟨10432620503147515019095073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27820321341726706717586861 10432620503147515019095073)
              ·
                refine ⟨7824465377360636264321305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10432620503147515019095073 7824465377360636264321305)
                ·
                  refine ⟨5868349033020477198240979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7824465377360636264321305 5868349033020477198240979)
                  ·
                    refine ⟨8802523549530715797361469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868349033020477198240979 8802523549530715797361469)
                    ·
                      refine ⟨3300946331074018424010551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802523549530715797361469 3300946331074018424010551)
                      ·
                        rfl

theorem cell23_6428570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6428570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428570 prefixEnd_6428570 := by exact prefixLift 6428570
  have htrace : WordTrace (prefixWord ++ tailWord_6428570) baseStart_6428570 baseEnd_6428570 := by
    simpa [prefixWord, tailWord_6428570, baseEnd_6428570] using wordTrace_append hprefix tailTrace_6428570
  have hstable : (prefixWord ++ tailWord_6428570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428570).length < 2 ^ (prefixWord ++ tailWord_6428570).sum := by decide
  have hdescent : baseEnd_6428570 < baseStart_6428570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428579 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_6428579 : Nat := 118140960795 + 6428579 * 2 ^ 59
def prefixEnd_6428579 : Nat := 4983230072969 + 3 ^ 40 * 6428579 * 2
def baseEnd_6428579 : Nat := 3300950952399908888798009

theorem tailTrace_6428579 : CollatzResearch.WordTrace tailWord_6428579 prefixEnd_6428579 3300950952399908888798009 := by
  unfold tailWord_6428579
  simp only [CollatzResearch.WordTrace]
  refine ⟨234469538577363671728920791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156313025718242447819280527 234469538577363671728920791)
  ·
    refine ⟨351704307866045507593381187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234469538577363671728920791 351704307866045507593381187)
    ·
      refine ⟨527556461799068261390071781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351704307866045507593381187 527556461799068261390071781)
      ·
        refine ⟨98916836587325299010638459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 527556461799068261390071781 98916836587325299010638459)
        ·
          refine ⟨148375254880987948515957689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98916836587325299010638459 148375254880987948515957689)
          ·
            refine ⟨111281441160740961386968267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148375254880987948515957689 111281441160740961386968267)
            ·
              refine ⟨166922161741111442080452401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111281441160740961386968267 166922161741111442080452401)
              ·
                refine ⟨125191621305833581560339301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166922161741111442080452401 125191621305833581560339301)
                ·
                  refine ⟨23473428994843796542563619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125191621305833581560339301 23473428994843796542563619)
                  ·
                    refine ⟨35210143492265694813845429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23473428994843796542563619 35210143492265694813845429)
                    ·
                      refine ⟨3300950952399908888798009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35210143492265694813845429 3300950952399908888798009)
                      ·
                        rfl

theorem cell23_6428579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_6428579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428579 prefixEnd_6428579 := by exact prefixLift 6428579
  have htrace : WordTrace (prefixWord ++ tailWord_6428579) baseStart_6428579 baseEnd_6428579 := by
    simpa [prefixWord, tailWord_6428579, baseEnd_6428579] using wordTrace_append hprefix tailTrace_6428579
  have hstable : (prefixWord ++ tailWord_6428579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428579).length < 2 ^ (prefixWord ++ tailWord_6428579).sum := by decide
  have hdescent : baseEnd_6428579 < baseStart_6428579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428633 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 7]
def baseStart_6428633 : Nat := 118140960795 + 6428633 * 2 ^ 59
def prefixEnd_6428633 : Nat := 4983230072969 + 3 ^ 40 * 6428633 * 2
def baseEnd_6428633 : Nat := 366775408928361297502529

theorem tailTrace_6428633 : CollatzResearch.WordTrace tailWord_6428633 prefixEnd_6428633 366775408928361297502529 := by
  unfold tailWord_6428633
  simp only [CollatzResearch.WordTrace]
  refine ⟨234471508119168038951386553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156314338746112025967591035 234471508119168038951386553)
  ·
    refine ⟨175853631089376029213539915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234471508119168038951386553 175853631089376029213539915)
    ·
      refine ⟨263780446634064043820309873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175853631089376029213539915 263780446634064043820309873)
      ·
        refine ⟨197835334975548032865232405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263780446634064043820309873 197835334975548032865232405)
        ·
          refine ⟨9273531326978814040557769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197835334975548032865232405 9273531326978814040557769)
          ·
            refine ⟨6955148495234110530418327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273531326978814040557769 6955148495234110530418327)
            ·
              refine ⟨10432722742851165795627491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955148495234110530418327 10432722742851165795627491)
              ·
                refine ⟨15649084114276748693441237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10432722742851165795627491 15649084114276748693441237)
                ·
                  refine ⟨366775408928361297502529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15649084114276748693441237 366775408928361297502529)
                  ·
                    rfl

theorem cell23_6428633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_6428633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428633 prefixEnd_6428633 := by exact prefixLift 6428633
  have htrace : WordTrace (prefixWord ++ tailWord_6428633) baseStart_6428633 baseEnd_6428633 := by
    simpa [prefixWord, tailWord_6428633, baseEnd_6428633] using wordTrace_append hprefix tailTrace_6428633
  have hstable : (prefixWord ++ tailWord_6428633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428633).length < 2 ^ (prefixWord ++ tailWord_6428633).sum := by decide
  have hdescent : baseEnd_6428633 < baseStart_6428633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428659 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 8]
def baseStart_6428659 : Nat := 118140960795 + 6428659 * 2 ^ 59
def prefixEnd_6428659 : Nat := 4983230072969 + 3 ^ 40 * 6428659 * 2
def baseEnd_6428659 : Nat := 1100330676950756191932547

theorem tailTrace_6428659 : CollatzResearch.WordTrace tailWord_6428659 prefixEnd_6428659 1100330676950756191932547 := by
  unfold tailWord_6428659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234472456417073845391833031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156314970944715896927888687 234472456417073845391833031)
  ·
    refine ⟨351708684625610768087749547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234472456417073845391833031 351708684625610768087749547)
    ·
      refine ⟨527563026938416152131624321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351708684625610768087749547 527563026938416152131624321)
      ·
        refine ⟨395672270203812114098718241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527563026938416152131624321 395672270203812114098718241)
        ·
          refine ⟨296754202652859085574038681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395672270203812114098718241 296754202652859085574038681)
          ·
            refine ⟨222565651989644314180529011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296754202652859085574038681 222565651989644314180529011)
            ·
              refine ⟨333848477984466471270793517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222565651989644314180529011 333848477984466471270793517)
              ·
                refine ⟨125193179244174926726547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333848477984466471270793517 125193179244174926726547569)
                ·
                  refine ⟨93894884433131195044910677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125193179244174926726547569 93894884433131195044910677)
                  ·
                    refine ⟨1100330676950756191932547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93894884433131195044910677 1100330676950756191932547)
                    ·
                      rfl

theorem cell23_6428659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_6428659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428659 prefixEnd_6428659 := by exact prefixLift 6428659
  have htrace : WordTrace (prefixWord ++ tailWord_6428659) baseStart_6428659 baseEnd_6428659 := by
    simpa [prefixWord, tailWord_6428659, baseEnd_6428659] using wordTrace_append hprefix tailTrace_6428659
  have hstable : (prefixWord ++ tailWord_6428659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428659).length < 2 ^ (prefixWord ++ tailWord_6428659).sum := by decide
  have hdescent : baseEnd_6428659 < baseStart_6428659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428683 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 4, 2]
def baseStart_6428683 : Nat := 118140960795 + 6428683 * 2 ^ 59
def prefixEnd_6428683 : Nat := 4983230072969 + 3 ^ 40 * 6428683 * 2
def baseEnd_6428683 : Nat := 3301004354387976481897531

theorem tailTrace_6428683 : CollatzResearch.WordTrace tailWord_6428683 prefixEnd_6428683 3301004354387976481897531 := by
  unfold tailWord_6428683
  simp only [CollatzResearch.WordTrace]
  refine ⟨234473331768986897490706703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156315554512657931660471135 234473331768986897490706703)
  ·
    refine ⟨351709997653480346236060055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234473331768986897490706703 351709997653480346236060055)
    ·
      refine ⟨527564996480220519354090083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351709997653480346236060055 527564996480220519354090083)
      ·
        refine ⟨791347494720330779031135125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527564996480220519354090083 791347494720330779031135125)
        ·
          refine ⟨37094413815015505267084459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 791347494720330779031135125 37094413815015505267084459)
          ·
            refine ⟨55641620722523257900626689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37094413815015505267084459 55641620722523257900626689)
            ·
              refine ⟨41731215541892443425470017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55641620722523257900626689 41731215541892443425470017)
              ·
                refine ⟨31298411656419332569102513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41731215541892443425470017 31298411656419332569102513)
                ·
                  refine ⟨23473808742314499426826885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31298411656419332569102513 23473808742314499426826885)
                  ·
                    refine ⟨4401339139183968642530041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23473808742314499426826885 4401339139183968642530041)
                    ·
                      refine ⟨3301004354387976481897531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401339139183968642530041 3301004354387976481897531)
                      ·
                        rfl

theorem cell23_6428683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4, 2].length) (baseStart_6428683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428683 prefixEnd_6428683 := by exact prefixLift 6428683
  have htrace : WordTrace (prefixWord ++ tailWord_6428683) baseStart_6428683 baseEnd_6428683 := by
    simpa [prefixWord, tailWord_6428683, baseEnd_6428683] using wordTrace_append hprefix tailTrace_6428683
  have hstable : (prefixWord ++ tailWord_6428683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428683).length < 2 ^ (prefixWord ++ tailWord_6428683).sum := by decide
  have hdescent : baseEnd_6428683 < baseStart_6428683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428686 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6428686 : Nat := 118140960795 + 6428686 * 2 ^ 59
def prefixEnd_6428686 : Nat := 4983230072969 + 3 ^ 40 * 6428686 * 2
def baseEnd_6428686 : Nat := 3301005894829939970160017

theorem tailTrace_6428686 : CollatzResearch.WordTrace tailWord_6428686 prefixEnd_6428686 3301005894829939970160017 := by
  unfold tailWord_6428686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309180148497003625383239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156315627458650686002043941 29309180148497003625383239)
  ·
    refine ⟨43963770222745505438074859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29309180148497003625383239 43963770222745505438074859)
    ·
      refine ⟨65945655334118258157112289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43963770222745505438074859 65945655334118258157112289)
      ·
        refine ⟨49459241500588693617834217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65945655334118258157112289 49459241500588693617834217)
        ·
          refine ⟨37094431125441520213375663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49459241500588693617834217 37094431125441520213375663)
          ·
            refine ⟨55641646688162280320063495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37094431125441520213375663 55641646688162280320063495)
            ·
              refine ⟨83462470032243420480095243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55641646688162280320063495 83462470032243420480095243)
              ·
                refine ⟨125193705048365130720142865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83462470032243420480095243 125193705048365130720142865)
                ·
                  refine ⟨93895278786273848040107149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125193705048365130720142865 93895278786273848040107149)
                  ·
                    refine ⟨35210729544852693015040181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93895278786273848040107149 35210729544852693015040181)
                    ·
                      refine ⟨3301005894829939970160017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35210729544852693015040181 3301005894829939970160017)
                      ·
                        rfl

theorem cell23_6428686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6428686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428686 prefixEnd_6428686 := by exact prefixLift 6428686
  have htrace : WordTrace (prefixWord ++ tailWord_6428686) baseStart_6428686 baseEnd_6428686 := by
    simpa [prefixWord, tailWord_6428686, baseEnd_6428686] using wordTrace_append hprefix tailTrace_6428686
  have hstable : (prefixWord ++ tailWord_6428686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428686).length < 2 ^ (prefixWord ++ tailWord_6428686).sum := by decide
  have hdescent : baseEnd_6428686 < baseStart_6428686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428700 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6428700 : Nat := 118140960795 + 6428700 * 2 ^ 59
def prefixEnd_6428700 : Nat := 4983230072969 + 3 ^ 40 * 6428700 * 2
def baseEnd_6428700 : Nat := 3301013083559102915384953

theorem tailTrace_6428700 : CollatzResearch.WordTrace tailWord_6428700 prefixEnd_6428700 3301013083559102915384953 := by
  unfold tailWord_6428700
  simp only [CollatzResearch.WordTrace]
  refine ⟨117236975904962654697037777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156315967873283539596050369 117236975904962654697037777)
  ·
    refine ⟨87927731928721991022778333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117236975904962654697037777 87927731928721991022778333)
    ·
      refine ⟨32972899473270746633541875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87927731928721991022778333 32972899473270746633541875)
      ·
        refine ⟨49459349209906119950312813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32972899473270746633541875 49459349209906119950312813)
        ·
          refine ⟨18547255953714794981367305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49459349209906119950312813 18547255953714794981367305)
          ·
            refine ⟨13910441965286096236025479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18547255953714794981367305 13910441965286096236025479)
            ·
              refine ⟨20865662947929144354038219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13910441965286096236025479 20865662947929144354038219)
              ·
                refine ⟨31298494421893716531057329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20865662947929144354038219 31298494421893716531057329)
                ·
                  refine ⟨23473870816420287398292997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31298494421893716531057329 23473870816420287398292997)
                  ·
                    refine ⟨4401350778078803887179937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23473870816420287398292997 4401350778078803887179937)
                    ·
                      refine ⟨3301013083559102915384953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401350778078803887179937 3301013083559102915384953)
                      ·
                        rfl

theorem cell23_6428700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6428700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428700 prefixEnd_6428700 := by exact prefixLift 6428700
  have htrace : WordTrace (prefixWord ++ tailWord_6428700) baseStart_6428700 baseEnd_6428700 := by
    simpa [prefixWord, tailWord_6428700, baseEnd_6428700] using wordTrace_append hprefix tailTrace_6428700
  have hstable : (prefixWord ++ tailWord_6428700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428700).length < 2 ^ (prefixWord ++ tailWord_6428700).sum := by decide
  have hdescent : baseEnd_6428700 < baseStart_6428700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428716 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_6428716 : Nat := 118140960795 + 6428716 * 2 ^ 59
def prefixEnd_6428716 : Nat := 4983230072969 + 3 ^ 40 * 6428716 * 2
def baseEnd_6428716 : Nat := 3301021299249574852784879

theorem tailTrace_6428716 : CollatzResearch.WordTrace tailWord_6428716 prefixEnd_6428716 3301021299249574852784879 := by
  unfold tailWord_6428716
  simp only [CollatzResearch.WordTrace]
  refine ⟨117237267688933672063329001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156316356918578229417772001 117237267688933672063329001)
  ·
    refine ⟨87927950766700254047496751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117237267688933672063329001 87927950766700254047496751)
    ·
      refine ⟨131891926150050381071245127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87927950766700254047496751 131891926150050381071245127)
      ·
        refine ⟨197837889225075571606867691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131891926150050381071245127 197837889225075571606867691)
        ·
          refine ⟨296756833837613357410301537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197837889225075571606867691 296756833837613357410301537)
          ·
            refine ⟨222567625378210018057726153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296756833837613357410301537 222567625378210018057726153)
            ·
              refine ⟨166925719033657513543294615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222567625378210018057726153 166925719033657513543294615)
              ·
                refine ⟨250388578550486270314941923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166925719033657513543294615 250388578550486270314941923)
                ·
                  refine ⟨375582867825729405472412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250388578550486270314941923 375582867825729405472412885)
                  ·
                    refine ⟨8802723464665532940759677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 375582867825729405472412885 8802723464665532940759677)
                    ·
                      refine ⟨3301021299249574852784879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802723464665532940759677 3301021299249574852784879)
                      ·
                        rfl

theorem cell23_6428716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_6428716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428716 prefixEnd_6428716 := by exact prefixLift 6428716
  have htrace : WordTrace (prefixWord ++ tailWord_6428716) baseStart_6428716 baseEnd_6428716 := by
    simpa [prefixWord, tailWord_6428716, baseEnd_6428716] using wordTrace_append hprefix tailTrace_6428716
  have hstable : (prefixWord ++ tailWord_6428716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428716).length < 2 ^ (prefixWord ++ tailWord_6428716).sum := by decide
  have hdescent : baseEnd_6428716 < baseStart_6428716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428720 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_6428720 : Nat := 118140960795 + 6428720 * 2 ^ 59
def prefixEnd_6428720 : Nat := 4983230072969 + 3 ^ 40 * 6428720 * 2
def baseEnd_6428720 : Nat := 3301023353172192837134861

theorem tailTrace_6428720 : CollatzResearch.WordTrace tailWord_6428720 prefixEnd_6428720 3301023353172192837134861 := by
  unfold tailWord_6428720
  simp only [CollatzResearch.WordTrace]
  refine ⟨117237340634926426404901807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156316454179901901873202409 117237340634926426404901807)
  ·
    refine ⟨175856010952389639607352711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117237340634926426404901807 175856010952389639607352711)
    ·
      refine ⟨263784016428584459411029067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175856010952389639607352711 263784016428584459411029067)
      ·
        refine ⟨395676024642876689116543601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263784016428584459411029067 395676024642876689116543601)
        ·
          refine ⟨296757018482157516837407701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395676024642876689116543601 296757018482157516837407701)
          ·
            refine ⟨6955242620675566800876743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296757018482157516837407701 6955242620675566800876743)
            ·
              refine ⟨10432863931013350201315115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955242620675566800876743 10432863931013350201315115)
              ·
                refine ⟨15649295896520025301972673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10432863931013350201315115 15649295896520025301972673)
                ·
                  refine ⟨11736971922390018976479505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15649295896520025301972673 11736971922390018976479505)
                  ·
                    refine ⟨8802728941792514232359629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11736971922390018976479505 8802728941792514232359629)
                    ·
                      refine ⟨3301023353172192837134861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802728941792514232359629 3301023353172192837134861)
                      ·
                        rfl

theorem cell23_6428720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_6428720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428720 prefixEnd_6428720 := by exact prefixLift 6428720
  have htrace : WordTrace (prefixWord ++ tailWord_6428720) baseStart_6428720 baseEnd_6428720 := by
    simpa [prefixWord, tailWord_6428720, baseEnd_6428720] using wordTrace_append hprefix tailTrace_6428720
  have hstable : (prefixWord ++ tailWord_6428720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428720).length < 2 ^ (prefixWord ++ tailWord_6428720).sum := by decide
  have hdescent : baseEnd_6428720 < baseStart_6428720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428750 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_6428750 : Nat := 118140960795 + 6428750 * 2 ^ 59
def prefixEnd_6428750 : Nat := 4983230072969 + 3 ^ 40 * 6428750 * 2
def baseEnd_6428750 : Nat := 3301038757591827719759723

theorem tailTrace_6428750 : CollatzResearch.WordTrace tailWord_6428750 prefixEnd_6428750 3301038757591827719759723 := by
  unfold tailWord_6428750
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309471932468020991674463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156317183639829445288930469 29309471932468020991674463)
  ·
    refine ⟨43964207898702031487511695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29309471932468020991674463 43964207898702031487511695)
    ·
      refine ⟨65946311848053047231267543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43964207898702031487511695 65946311848053047231267543)
      ·
        refine ⟨98919467772079570846901315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65946311848053047231267543 98919467772079570846901315)
        ·
          refine ⟨148379201658119356270351973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98919467772079570846901315 148379201658119356270351973)
          ·
            refine ⟨27821100310897379300690995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148379201658119356270351973 27821100310897379300690995)
            ·
              refine ⟨41731650466346068951036493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27821100310897379300690995 41731650466346068951036493)
              ·
                refine ⟨15649368924879775856638685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41731650466346068951036493 15649368924879775856638685)
                ·
                  refine ⟨5868513346829915946239507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15649368924879775856638685 5868513346829915946239507)
                  ·
                    refine ⟨8802770020244873919359261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868513346829915946239507 8802770020244873919359261)
                    ·
                      refine ⟨3301038757591827719759723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802770020244873919359261 3301038757591827719759723)
                      ·
                        rfl

theorem cell23_6428750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_6428750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428750 prefixEnd_6428750 := by exact prefixLift 6428750
  have htrace : WordTrace (prefixWord ++ tailWord_6428750) baseStart_6428750 baseEnd_6428750 := by
    simpa [prefixWord, tailWord_6428750, baseEnd_6428750] using wordTrace_append hprefix tailTrace_6428750
  have hstable : (prefixWord ++ tailWord_6428750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428750).length < 2 ^ (prefixWord ++ tailWord_6428750).sum := by decide
  have hdescent : baseEnd_6428750 < baseStart_6428750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428783 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 4, 4]
def baseStart_6428783 : Nat := 118140960795 + 6428783 * 2 ^ 59
def prefixEnd_6428783 : Nat := 4983230072969 + 3 ^ 40 * 6428783 * 2
def baseEnd_6428783 : Nat := 1100351900817808696882357

theorem tailTrace_6428783 : CollatzResearch.WordTrace tailWord_6428783 prefixEnd_6428783 1100351900817808696882357 := by
  unfold tailWord_6428783
  simp only [CollatzResearch.WordTrace]
  refine ⟨234476979068624614569347003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156317986045749743046231335 234476979068624614569347003)
  ·
    refine ⟨351715468602936921854020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234476979068624614569347003 351715468602936921854020505)
    ·
      refine ⟨263786601452202691390515379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351715468602936921854020505 263786601452202691390515379)
      ·
        refine ⟨395679902178304037085773069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263786601452202691390515379 395679902178304037085773069)
        ·
          refine ⟨148379963316864013907164901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395679902178304037085773069 148379963316864013907164901)
          ·
            refine ⟨27821243121912002607593419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148379963316864013907164901 27821243121912002607593419)
            ·
              refine ⟨41731864682868003911390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27821243121912002607593419 41731864682868003911390129)
              ·
                refine ⟨31298898512151002933542597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41731864682868003911390129 31298898512151002933542597)
                ·
                  refine ⟨5868543471028313050039237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31298898512151002933542597 5868543471028313050039237)
                  ·
                    refine ⟨1100351900817808696882357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868543471028313050039237 1100351900817808696882357)
                    ·
                      rfl

theorem cell23_6428783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_6428783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428783 prefixEnd_6428783 := by exact prefixLift 6428783
  have htrace : WordTrace (prefixWord ++ tailWord_6428783) baseStart_6428783 baseEnd_6428783 := by
    simpa [prefixWord, tailWord_6428783, baseEnd_6428783] using wordTrace_append hprefix tailTrace_6428783
  have hstable : (prefixWord ++ tailWord_6428783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428783).length < 2 ^ (prefixWord ++ tailWord_6428783).sum := by decide
  have hdescent : baseEnd_6428783 < baseStart_6428783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428784 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 1, 1, 3]
def baseStart_6428784 : Nat := 118140960795 + 6428784 * 2 ^ 59
def prefixEnd_6428784 : Nat := 4983230072969 + 3 ^ 40 * 6428784 * 2
def baseEnd_6428784 : Nat := 3301056215934080586734567

theorem tailTrace_6428784 : CollatzResearch.WordTrace tailWord_6428784 prefixEnd_6428784 3301056215934080586734567 := by
  unfold tailWord_6428784
  simp only [CollatzResearch.WordTrace]
  refine ⟨117238507770810495870066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156318010361080661160088937 117238507770810495870066703)
  ·
    refine ⟨175857761656215743805100055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117238507770810495870066703 175857761656215743805100055)
    ·
      refine ⟨263786642484323615707650083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175857761656215743805100055 263786642484323615707650083)
      ·
        refine ⟨395679963726485423561475125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263786642484323615707650083 395679963726485423561475125)
        ·
          refine ⟨37094996599358008458888293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395679963726485423561475125 37094996599358008458888293)
          ·
            refine ⟨6955311862379626586041555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37094996599358008458888293 6955311862379626586041555)
            ·
              refine ⟨10432967793569439879062333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955311862379626586041555 10432967793569439879062333)
              ·
                refine ⟨3912362922588539954648375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10432967793569439879062333 3912362922588539954648375)
                ·
                  refine ⟨5868544383882809931972563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912362922588539954648375 5868544383882809931972563)
                  ·
                    refine ⟨8802816575824214897958845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868544383882809931972563 8802816575824214897958845)
                    ·
                      refine ⟨3301056215934080586734567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802816575824214897958845 3301056215934080586734567)
                      ·
                        rfl

theorem cell23_6428784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 1, 3].length) (baseStart_6428784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428784 prefixEnd_6428784 := by exact prefixLift 6428784
  have htrace : WordTrace (prefixWord ++ tailWord_6428784) baseStart_6428784 baseEnd_6428784 := by
    simpa [prefixWord, tailWord_6428784, baseEnd_6428784] using wordTrace_append hprefix tailTrace_6428784
  have hstable : (prefixWord ++ tailWord_6428784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428784).length < 2 ^ (prefixWord ++ tailWord_6428784).sum := by decide
  have hdescent : baseEnd_6428784 < baseStart_6428784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428793 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6428793 : Nat := 118140960795 + 6428793 * 2 ^ 59
def prefixEnd_6428793 : Nat := 4983230072969 + 3 ^ 40 * 6428793 * 2
def baseEnd_6428793 : Nat := 3301060837259971051522025

theorem tailTrace_6428793 : CollatzResearch.WordTrace tailWord_6428793 prefixEnd_6428793 3301060837259971051522025 := by
  unfold tailWord_6428793
  simp only [CollatzResearch.WordTrace]
  refine ⟨234477343798588386277211033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156318229199058924184807355 234477343798588386277211033)
  ·
    refine ⟨175858007848941289707908275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234477343798588386277211033 175858007848941289707908275)
    ·
      refine ⟨263787011773411934561862413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175858007848941289707908275 263787011773411934561862413)
      ·
        refine ⟨98920129415029475460698405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263787011773411934561862413 98920129415029475460698405)
        ·
          refine ⟨18547524265318026648880951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98920129415029475460698405 18547524265318026648880951)
          ·
            refine ⟨27821286397977039973321427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18547524265318026648880951 27821286397977039973321427)
            ·
              refine ⟨41731929596965559959982141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27821286397977039973321427 41731929596965559959982141)
              ·
                refine ⟨15649473598862084984993303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41731929596965559959982141 15649473598862084984993303)
                ·
                  refine ⟨23474210398293127477489955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15649473598862084984993303 23474210398293127477489955)
                  ·
                    refine ⟨35211315597439691216234933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23474210398293127477489955 35211315597439691216234933)
                    ·
                      refine ⟨3301060837259971051522025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35211315597439691216234933 3301060837259971051522025)
                      ·
                        rfl

theorem cell23_6428793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6428793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428793 prefixEnd_6428793 := by exact prefixLift 6428793
  have htrace : WordTrace (prefixWord ++ tailWord_6428793) baseStart_6428793 baseEnd_6428793 := by
    simpa [prefixWord, tailWord_6428793, baseEnd_6428793] using wordTrace_append hprefix tailTrace_6428793
  have hstable : (prefixWord ++ tailWord_6428793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428793).length < 2 ^ (prefixWord ++ tailWord_6428793).sum := by decide
  have hdescent : baseEnd_6428793 < baseStart_6428793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428796 : List Nat := [2, 2, 2, 1, 1, 4, 11]
def baseStart_6428796 : Nat := 118140960795 + 6428796 * 2 ^ 59
def prefixEnd_6428796 : Nat := 4983230072969 + 3 ^ 40 * 6428796 * 2
def baseEnd_6428796 : Nat := 40753856514838698022031

theorem tailTrace_6428796 : CollatzResearch.WordTrace tailWord_6428796 prefixEnd_6428796 40753856514838698022031 := by
  unfold tailWord_6428796
  simp only [CollatzResearch.WordTrace]
  refine ⟨117238726608788758894785121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156318302145051678526380161 117238726608788758894785121)
  ·
    refine ⟨87929044956591569171088841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117238726608788758894785121 87929044956591569171088841)
    ·
      refine ⟨65946783717443676878316631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87929044956591569171088841 65946783717443676878316631)
      ·
        refine ⟨98920175576165515317474947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65946783717443676878316631 98920175576165515317474947)
        ·
          refine ⟨148380263364248272976212421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98920175576165515317474947 148380263364248272976212421)
          ·
            refine ⟨27821299380796551183039829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148380263364248272976212421 27821299380796551183039829)
            ·
              refine ⟨40753856514838698022031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27821299380796551183039829 40753856514838698022031)
              ·
                rfl

theorem cell23_6428796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 11].length) (baseStart_6428796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428796 prefixEnd_6428796 := by exact prefixLift 6428796
  have htrace : WordTrace (prefixWord ++ tailWord_6428796) baseStart_6428796 baseEnd_6428796 := by
    simpa [prefixWord, tailWord_6428796, baseEnd_6428796] using wordTrace_append hprefix tailTrace_6428796
  have hstable : (prefixWord ++ tailWord_6428796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428796).length < 2 ^ (prefixWord ++ tailWord_6428796).sum := by decide
  have hdescent : baseEnd_6428796 < baseStart_6428796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428801 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6428801 : Nat := 118140960795 + 6428801 * 2 ^ 59
def prefixEnd_6428801 : Nat := 4983230072969 + 3 ^ 40 * 6428801 * 2
def baseEnd_6428801 : Nat := 3301064945105207020221989

theorem tailTrace_6428801 : CollatzResearch.WordTrace tailWord_6428801 prefixEnd_6428801 3301064945105207020221989 := by
  unfold tailWord_6428801
  simp only [CollatzResearch.WordTrace]
  refine ⟨234477635582559403643502257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156318423721706269095668171 234477635582559403643502257)
  ·
    refine ⟨175858226686919552732626693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234477635582559403643502257 175858226686919552732626693)
    ·
      refine ⟨32973417503797416137367505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175858226686919552732626693 32973417503797416137367505)
      ·
        refine ⟨24730063127848062103025629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32973417503797416137367505 24730063127848062103025629)
        ·
          refine ⟨9273773672943023288634611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24730063127848062103025629 9273773672943023288634611)
          ·
            refine ⟨13910660509414534932951917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273773672943023288634611 13910660509414534932951917)
            ·
              refine ⟨5216497691030450599856969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13910660509414534932951917 5216497691030450599856969)
              ·
                refine ⟨3912373268272837949892727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216497691030450599856969 3912373268272837949892727)
                ·
                  refine ⟨5868559902409256924839091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912373268272837949892727 5868559902409256924839091)
                  ·
                    refine ⟨8802839853613885387258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868559902409256924839091 8802839853613885387258637)
                    ·
                      refine ⟨3301064945105207020221989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802839853613885387258637 3301064945105207020221989)
                      ·
                        rfl

theorem cell23_6428801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6428801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428801 prefixEnd_6428801 := by exact prefixLift 6428801
  have htrace : WordTrace (prefixWord ++ tailWord_6428801) baseStart_6428801 baseEnd_6428801 := by
    simpa [prefixWord, tailWord_6428801, baseEnd_6428801] using wordTrace_append hprefix tailTrace_6428801
  have hstable : (prefixWord ++ tailWord_6428801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428801).length < 2 ^ (prefixWord ++ tailWord_6428801).sum := by decide
  have hdescent : baseEnd_6428801 < baseStart_6428801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428807 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_6428807 : Nat := 118140960795 + 6428807 * 2 ^ 59
def prefixEnd_6428807 : Nat := 4983230072969 + 3 ^ 40 * 6428807 * 2
def baseEnd_6428807 : Nat := 3301068025989133996746961

theorem tailTrace_6428807 : CollatzResearch.WordTrace tailWord_6428807 prefixEnd_6428807 3301068025989133996746961 := by
  unfold tailWord_6428807
  simp only [CollatzResearch.WordTrace]
  refine ⟨234477854420537666668220675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156318569613691777778813783 234477854420537666668220675)
  ·
    refine ⟨351716781630806500002331013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234477854420537666668220675 351716781630806500002331013)
    ·
      refine ⟨65946896555776218750437065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351716781630806500002331013 65946896555776218750437065)
      ·
        refine ⟨49460172416832164062827799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65946896555776218750437065 49460172416832164062827799)
        ·
          refine ⟨74190258625248246094241699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49460172416832164062827799 74190258625248246094241699)
          ·
            refine ⟨111285387937872369141362549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74190258625248246094241699 111285387937872369141362549)
            ·
              refine ⟨10433005119175534607002739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111285387937872369141362549 10433005119175534607002739)
              ·
                refine ⟨15649507678763301910504109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10433005119175534607002739 15649507678763301910504109)
                ·
                  refine ⟨5868565379536238216439041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15649507678763301910504109 5868565379536238216439041)
                  ·
                    refine ⟨4401424034652178662329281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868565379536238216439041 4401424034652178662329281)
                    ·
                      refine ⟨3301068025989133996746961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401424034652178662329281 3301068025989133996746961)
                      ·
                        rfl

theorem cell23_6428807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_6428807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428807 prefixEnd_6428807 := by exact prefixLift 6428807
  have htrace : WordTrace (prefixWord ++ tailWord_6428807) baseStart_6428807 baseEnd_6428807 := by
    simpa [prefixWord, tailWord_6428807, baseEnd_6428807] using wordTrace_append hprefix tailTrace_6428807
  have hstable : (prefixWord ++ tailWord_6428807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428807).length < 2 ^ (prefixWord ++ tailWord_6428807).sum := by decide
  have hdescent : baseEnd_6428807 < baseStart_6428807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428816 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_6428816 : Nat := 118140960795 + 6428816 * 2 ^ 59
def prefixEnd_6428816 : Nat := 4983230072969 + 3 ^ 40 * 6428816 * 2
def baseEnd_6428816 : Nat := 3301072647315024461534419

theorem tailTrace_6428816 : CollatzResearch.WordTrace tailWord_6428816 prefixEnd_6428816 3301072647315024461534419 := by
  unfold tailWord_6428816
  simp only [CollatzResearch.WordTrace]
  refine ⟨117239091338752530602649151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156318788451670040803532201 117239091338752530602649151)
  ·
    refine ⟨175858637008128795903973727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117239091338752530602649151 175858637008128795903973727)
    ·
      refine ⟨263787955512193193855960591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175858637008128795903973727 263787955512193193855960591)
      ·
        refine ⟨395681933268289790783940887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263787955512193193855960591 395681933268289790783940887)
        ·
          refine ⟨593522899902434686175911331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395681933268289790783940887 593522899902434686175911331)
          ·
            refine ⟨890284349853652029263866997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593522899902434686175911331 890284349853652029263866997)
            ·
              refine ⟨83464157798779877743487531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 890284349853652029263866997 83464157798779877743487531)
              ·
                refine ⟨125196236698169816615231297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83464157798779877743487531 125196236698169816615231297)
                ·
                  refine ⟨93897177523627362461423473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125196236698169816615231297 93897177523627362461423473)
                  ·
                    refine ⟨70422883142720521846067605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93897177523627362461423473 70422883142720521846067605)
                    ·
                      refine ⟨3301072647315024461534419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70422883142720521846067605 3301072647315024461534419)
                      ·
                        rfl

theorem cell23_6428816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_6428816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428816 prefixEnd_6428816 := by exact prefixLift 6428816
  have htrace : WordTrace (prefixWord ++ tailWord_6428816) baseStart_6428816 baseEnd_6428816 := by
    simpa [prefixWord, tailWord_6428816, baseEnd_6428816] using wordTrace_append hprefix tailTrace_6428816
  have hstable : (prefixWord ++ tailWord_6428816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428816).length < 2 ^ (prefixWord ++ tailWord_6428816).sum := by decide
  have hdescent : baseEnd_6428816 < baseStart_6428816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428824 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6428824 : Nat := 118140960795 + 6428824 * 2 ^ 59
def prefixEnd_6428824 : Nat := 4983230072969 + 3 ^ 40 * 6428824 * 2
def baseEnd_6428824 : Nat := 3301076755160260430234383

theorem tailTrace_6428824 : CollatzResearch.WordTrace tailWord_6428824 prefixEnd_6428824 3301076755160260430234383 := by
  unfold tailWord_6428824
  simp only [CollatzResearch.WordTrace]
  refine ⟨117239237230738039285794763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156318982974317385714393017 117239237230738039285794763)
  ·
    refine ⟨175858855846107058928692145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117239237230738039285794763 175858855846107058928692145)
    ·
      refine ⟨131894141884580294196519109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175858855846107058928692145 131894141884580294196519109)
      ·
        refine ⟨24730151603358805161847333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131894141884580294196519109 24730151603358805161847333)
        ·
          refine ⟨4636903425629775967846375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24730151603358805161847333 4636903425629775967846375)
          ·
            refine ⟨6955355138444663951769563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636903425629775967846375 6955355138444663951769563)
            ·
              refine ⟨10433032707666995927654345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955355138444663951769563 10433032707666995927654345)
              ·
                refine ⟨7824774530750246945740759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433032707666995927654345 7824774530750246945740759)
                ·
                  refine ⟨11737161796125370418611139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7824774530750246945740759 11737161796125370418611139)
                  ·
                    refine ⟨17605742694188055627916709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11737161796125370418611139 17605742694188055627916709)
                    ·
                      refine ⟨3301076755160260430234383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17605742694188055627916709 3301076755160260430234383)
                      ·
                        rfl

theorem cell23_6428824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6428824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428824 prefixEnd_6428824 := by exact prefixLift 6428824
  have htrace : WordTrace (prefixWord ++ tailWord_6428824) baseStart_6428824 baseEnd_6428824 := by
    simpa [prefixWord, tailWord_6428824, baseEnd_6428824] using wordTrace_append hprefix tailTrace_6428824
  have hstable : (prefixWord ++ tailWord_6428824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428824).length < 2 ^ (prefixWord ++ tailWord_6428824).sum := by decide
  have hdescent : baseEnd_6428824 < baseStart_6428824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428852 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6428852 : Nat := 118140960795 + 6428852 * 2 ^ 59
def prefixEnd_6428852 : Nat := 4983230072969 + 3 ^ 40 * 6428852 * 2
def baseEnd_6428852 : Nat := 3301091132618586320684255

theorem tailTrace_6428852 : CollatzResearch.WordTrace tailWord_6428852 prefixEnd_6428852 3301091132618586320684255 := by
  unfold tailWord_6428852
  simp only [CollatzResearch.WordTrace]
  refine ⟨117239747852687319676804405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156319663803583092902405873 117239747852687319676804405)
  ·
    refine ⟨10991226361189436219700413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117239747852687319676804405 10991226361189436219700413)
    ·
      refine ⟨4121709885446038582387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10991226361189436219700413 4121709885446038582387655)
      ·
        refine ⟨6182564828169057873581483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121709885446038582387655 6182564828169057873581483)
        ·
          refine ⟨9273847242253586810372225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182564828169057873581483 9273847242253586810372225)
          ·
            refine ⟨6955385431690190107779169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273847242253586810372225 6955385431690190107779169)
            ·
              refine ⟨5216539073767642580834377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955385431690190107779169 5216539073767642580834377)
              ·
                refine ⟨3912404305325731935625783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216539073767642580834377 3912404305325731935625783)
                ·
                  refine ⟨5868606457988597903438675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912404305325731935625783 5868606457988597903438675)
                  ·
                    refine ⟨8802909686982896855158013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868606457988597903438675 8802909686982896855158013)
                    ·
                      refine ⟨3301091132618586320684255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802909686982896855158013 3301091132618586320684255)
                      ·
                        rfl

theorem cell23_6428852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6428852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428852 prefixEnd_6428852 := by exact prefixLift 6428852
  have htrace : WordTrace (prefixWord ++ tailWord_6428852) baseStart_6428852 baseEnd_6428852 := by
    simpa [prefixWord, tailWord_6428852, baseEnd_6428852] using wordTrace_append hprefix tailTrace_6428852
  have hstable : (prefixWord ++ tailWord_6428852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428852).length < 2 ^ (prefixWord ++ tailWord_6428852).sum := by decide
  have hdescent : baseEnd_6428852 < baseStart_6428852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428857 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6428857 : Nat := 118140960795 + 6428857 * 2 ^ 59
def prefixEnd_6428857 : Nat := 4983230072969 + 3 ^ 40 * 6428857 * 2
def baseEnd_6428857 : Nat := 3301093700021858801121731

theorem tailTrace_6428857 : CollatzResearch.WordTrace tailWord_6428857 prefixEnd_6428857 3301093700021858801121731 := by
  unfold tailWord_6428857
  simp only [CollatzResearch.WordTrace]
  refine ⟨234479678070356525207540825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156319785380237683471693883 234479678070356525207540825)
  ·
    refine ⟨175859758552767393905655619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234479678070356525207540825 175859758552767393905655619)
    ·
      refine ⟨263789637829151090858483429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175859758552767393905655619 263789637829151090858483429)
      ·
        refine ⟨49460557092965829535965643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263789637829151090858483429 49460557092965829535965643)
        ·
          refine ⟨74190835639448744303948465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49460557092965829535965643 74190835639448744303948465)
          ·
            refine ⟨55643126729586558227961349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74190835639448744303948465 55643126729586558227961349)
            ·
              refine ⟨10433086261797479667742753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55643126729586558227961349 10433086261797479667742753)
              ·
                refine ⟨7824814696348109750807065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433086261797479667742753 7824814696348109750807065)
                ·
                  refine ⟨5868611022261082313105299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7824814696348109750807065 5868611022261082313105299)
                  ·
                    refine ⟨8802916533391623469657949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868611022261082313105299 8802916533391623469657949)
                    ·
                      refine ⟨3301093700021858801121731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8802916533391623469657949 3301093700021858801121731)
                      ·
                        rfl

theorem cell23_6428857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6428857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428857 prefixEnd_6428857 := by exact prefixLift 6428857
  have htrace : WordTrace (prefixWord ++ tailWord_6428857) baseStart_6428857 baseEnd_6428857 := by
    simpa [prefixWord, tailWord_6428857, baseEnd_6428857] using wordTrace_append hprefix tailTrace_6428857
  have hstable : (prefixWord ++ tailWord_6428857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428857).length < 2 ^ (prefixWord ++ tailWord_6428857).sum := by decide
  have hdescent : baseEnd_6428857 < baseStart_6428857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428897 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_6428897 : Nat := 118140960795 + 6428897 * 2 ^ 59
def prefixEnd_6428897 : Nat := 4983230072969 + 3 ^ 40 * 6428897 * 2
def baseEnd_6428897 : Nat := 3301114239248038644621547

theorem tailTrace_6428897 : CollatzResearch.WordTrace tailWord_6428897 prefixEnd_6428897 3301114239248038644621547 := by
  unfold tailWord_6428897
  simp only [CollatzResearch.WordTrace]
  refine ⟨234481136990211612038996945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156320757993474408025997963 234481136990211612038996945)
  ·
    refine ⟨175860852742658709029247709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234481136990211612038996945 175860852742658709029247709)
    ·
      refine ⟨65947819778497015885967891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175860852742658709029247709 65947819778497015885967891)
      ·
        refine ⟨98921729667745523828951837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65947819778497015885967891 98921729667745523828951837)
        ·
          refine ⟨37095648625404571435856939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98921729667745523828951837 37095648625404571435856939)
          ·
            refine ⟨55643472938106857153785409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37095648625404571435856939 55643472938106857153785409)
            ·
              refine ⟨41732604703580142865339057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55643472938106857153785409 41732604703580142865339057)
              ·
                refine ⟨31299453527685107149004293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41732604703580142865339057 31299453527685107149004293)
                ·
                  refine ⟨5868647536440957590438305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31299453527685107149004293 5868647536440957590438305)
                  ·
                    refine ⟨4401485652330718192828729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868647536440957590438305 4401485652330718192828729)
                    ·
                      refine ⟨3301114239248038644621547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401485652330718192828729 3301114239248038644621547)
                      ·
                        rfl

theorem cell23_6428897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_6428897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428897 prefixEnd_6428897 := by exact prefixLift 6428897
  have htrace : WordTrace (prefixWord ++ tailWord_6428897) baseStart_6428897 baseEnd_6428897 := by
    simpa [prefixWord, tailWord_6428897, baseEnd_6428897] using wordTrace_append hprefix tailTrace_6428897
  have hstable : (prefixWord ++ tailWord_6428897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428897).length < 2 ^ (prefixWord ++ tailWord_6428897).sum := by decide
  have hdescent : baseEnd_6428897 < baseStart_6428897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428901 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6428901 : Nat := 118140960795 + 6428901 * 2 ^ 59
def prefixEnd_6428901 : Nat := 4983230072969 + 3 ^ 40 * 6428901 * 2
def baseEnd_6428901 : Nat := 3301116293170656628971529

theorem tailTrace_6428901 : CollatzResearch.WordTrace tailWord_6428901 prefixEnd_6428901 3301116293170656628971529 := by
  unfold tailWord_6428901
  simp only [CollatzResearch.WordTrace]
  refine ⟨234481282882197120722142557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156320855254798080481428371 234481282882197120722142557)
  ·
    refine ⟨87930481080823920270803459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234481282882197120722142557 87930481080823920270803459)
    ·
      refine ⟨131895721621235880406205189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87930481080823920270803459 131895721621235880406205189)
      ·
        refine ⟨24730447803981727576163473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131895721621235880406205189 24730447803981727576163473)
        ·
          refine ⟨18547835852986295682122605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24730447803981727576163473 18547835852986295682122605)
          ·
            refine ⟨6955438444869860880795977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18547835852986295682122605 6955438444869860880795977)
            ·
              refine ⟨5216578833652395660596983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955438444869860880795977 5216578833652395660596983)
              ·
                refine ⟨7824868250478593490895475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216578833652395660596983 7824868250478593490895475)
                ·
                  refine ⟨11737302375717890236343213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7824868250478593490895475 11737302375717890236343213)
                  ·
                    refine ⟨4401488390894208838628705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11737302375717890236343213 4401488390894208838628705)
                    ·
                      refine ⟨3301116293170656628971529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401488390894208838628705 3301116293170656628971529)
                      ·
                        rfl

theorem cell23_6428901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6428901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428901 prefixEnd_6428901 := by exact prefixLift 6428901
  have htrace : WordTrace (prefixWord ++ tailWord_6428901) baseStart_6428901 baseEnd_6428901 := by
    simpa [prefixWord, tailWord_6428901, baseEnd_6428901] using wordTrace_append hprefix tailTrace_6428901
  have hstable : (prefixWord ++ tailWord_6428901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428901).length < 2 ^ (prefixWord ++ tailWord_6428901).sum := by decide
  have hdescent : baseEnd_6428901 < baseStart_6428901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428914 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6428914 : Nat := 118140960795 + 6428914 * 2 ^ 59
def prefixEnd_6428914 : Nat := 4983230072969 + 3 ^ 40 * 6428914 * 2
def baseEnd_6428914 : Nat := 3301122968419165078108969

theorem tailTrace_6428914 : CollatzResearch.WordTrace tailWord_6428914 prefixEnd_6428914 3301122968419165078108969 := by
  unfold tailWord_6428914
  simp only [CollatzResearch.WordTrace]
  refine ⟨58620439257787505985591449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156321171354100015961577197 58620439257787505985591449)
  ·
    refine ⟨43965329443340629489193587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58620439257787505985591449 43965329443340629489193587)
    ·
      refine ⟨65947994165010944233790381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43965329443340629489193587 65947994165010944233790381)
      ·
        refine ⟨24730497811879104087671393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65947994165010944233790381 24730497811879104087671393)
        ·
          refine ⟨18547873358909328065753545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24730497811879104087671393 18547873358909328065753545)
          ·
            refine ⟨13910905019181996049315159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18547873358909328065753545 13910905019181996049315159)
            ·
              refine ⟨20866357528772994073972739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13910905019181996049315159 20866357528772994073972739)
              ·
                refine ⟨31299536293159491110959109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20866357528772994073972739 31299536293159491110959109)
                ·
                  refine ⟨5868663054967404583304833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31299536293159491110959109 5868663054967404583304833)
                  ·
                    refine ⟨4401497291225553437478625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868663054967404583304833 4401497291225553437478625)
                    ·
                      refine ⟨3301122968419165078108969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401497291225553437478625 3301122968419165078108969)
                      ·
                        rfl

theorem cell23_6428914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6428914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428914 prefixEnd_6428914 := by exact prefixLift 6428914
  have htrace : WordTrace (prefixWord ++ tailWord_6428914) baseStart_6428914 baseEnd_6428914 := by
    simpa [prefixWord, tailWord_6428914, baseEnd_6428914] using wordTrace_append hprefix tailTrace_6428914
  have hstable : (prefixWord ++ tailWord_6428914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428914).length < 2 ^ (prefixWord ++ tailWord_6428914).sum := by decide
  have hdescent : baseEnd_6428914 < baseStart_6428914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428933 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_6428933 : Nat := 118140960795 + 6428933 * 2 ^ 59
def prefixEnd_6428933 : Nat := 4983230072969 + 3 ^ 40 * 6428933 * 2
def baseEnd_6428933 : Nat := 1100377574850533501257127

theorem tailTrace_6428933 : CollatzResearch.WordTrace tailWord_6428933 prefixEnd_6428933 1100377574850533501257127 := by
  unfold tailWord_6428933
  simp only [CollatzResearch.WordTrace]
  refine ⟨234482450018081190187307453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156321633345387460124871635 234482450018081190187307453)
  ·
    refine ⟨87930918756780446320240295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234482450018081190187307453 87930918756780446320240295)
    ·
      refine ⟨131896378135170669480360443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87930918756780446320240295 131896378135170669480360443)
      ·
        refine ⟨197844567202756004220540665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131896378135170669480360443 197844567202756004220540665)
        ·
          refine ⟨148383425402067003165405499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197844567202756004220540665 148383425402067003165405499)
          ·
            refine ⟨222575138103100504748108249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148383425402067003165405499 222575138103100504748108249)
            ·
              refine ⟨166931353577325378561081187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222575138103100504748108249 166931353577325378561081187)
              ·
                refine ⟨250397030365988067841621781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166931353577325378561081187 250397030365988067841621781)
                ·
                  refine ⟨11737360798405690680076021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250397030365988067841621781 11737360798405690680076021)
                  ·
                    refine ⟨1100377574850533501257127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11737360798405690680076021 1100377574850533501257127)
                    ·
                      rfl

theorem cell23_6428933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_6428933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428933 prefixEnd_6428933 := by exact prefixLift 6428933
  have htrace : WordTrace (prefixWord ++ tailWord_6428933) baseStart_6428933 baseEnd_6428933 := by
    simpa [prefixWord, tailWord_6428933, baseEnd_6428933] using wordTrace_append hprefix tailTrace_6428933
  have hstable : (prefixWord ++ tailWord_6428933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428933).length < 2 ^ (prefixWord ++ tailWord_6428933).sum := by decide
  have hdescent : baseEnd_6428933 < baseStart_6428933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428954 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_6428954 : Nat := 118140960795 + 6428954 * 2 ^ 59
def prefixEnd_6428954 : Nat := 4983230072969 + 3 ^ 40 * 6428954 * 2
def baseEnd_6428954 : Nat := 366793723071704991289865

theorem tailTrace_6428954 : CollatzResearch.WordTrace tailWord_6428954 prefixEnd_6428954 366793723071704991289865 := by
  unfold tailWord_6428954
  simp only [CollatzResearch.WordTrace]
  refine ⟨58620803987751277693455479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156322143967336740515881277 58620803987751277693455479)
  ·
    refine ⟨87931205981626916540183219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58620803987751277693455479 87931205981626916540183219)
    ·
      refine ⟨131896808972440374810274829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87931205981626916540183219 131896808972440374810274829)
      ·
        refine ⟨49461303364665140553853061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131896808972440374810274829 49461303364665140553853061)
        ·
          refine ⟨9273994380874713853847449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49461303364665140553853061 9273994380874713853847449)
          ·
            refine ⟨6955495785656035390385587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273994380874713853847449 6955495785656035390385587)
            ·
              refine ⟨10433243678484053085578381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955495785656035390385587 10433243678484053085578381)
              ·
                refine ⟨3912466379431519907091893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10433243678484053085578381 3912466379431519907091893)
                ·
                  refine ⟨366793723071704991289865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912466379431519907091893 366793723071704991289865)
                  ·
                    rfl

theorem cell23_6428954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_6428954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428954 prefixEnd_6428954 := by exact prefixLift 6428954
  have htrace : WordTrace (prefixWord ++ tailWord_6428954) baseStart_6428954 baseEnd_6428954 := by
    simpa [prefixWord, tailWord_6428954, baseEnd_6428954] using wordTrace_append hprefix tailTrace_6428954
  have hstable : (prefixWord ++ tailWord_6428954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428954).length < 2 ^ (prefixWord ++ tailWord_6428954).sum := by decide
  have hdescent : baseEnd_6428954 < baseStart_6428954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6428983 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_6428983 : Nat := 118140960795 + 6428983 * 2 ^ 59
def prefixEnd_6428983 : Nat := 4983230072969 + 3 ^ 40 * 6428983 * 2
def baseEnd_6428983 : Nat := 3301158398584325308146151

theorem tailTrace_6428983 : CollatzResearch.WordTrace tailWord_6428983 prefixEnd_6428983 3301158398584325308146151 := by
  unfold tailWord_6428983
  simp only [CollatzResearch.WordTrace]
  refine ⟨234484273667900048726627603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156322849111933365817751735 234484273667900048726627603)
  ·
    refine ⟨351726410501850073089941405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234484273667900048726627603 351726410501850073089941405)
    ·
      refine ⟨131897403938193777408728027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351726410501850073089941405 131897403938193777408728027)
      ·
        refine ⟨197846105907290666113092041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131897403938193777408728027 197846105907290666113092041)
        ·
          refine ⟨148384579430467999584819031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197846105907290666113092041 148384579430467999584819031)
          ·
            refine ⟨222576869145701999377228547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148384579430467999584819031 222576869145701999377228547)
            ·
              refine ⟨333865303718552999065842821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222576869145701999377228547 333865303718552999065842821)
              ·
                refine ⟨62599744447228687324845529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333865303718552999065842821 62599744447228687324845529)
                ·
                  refine ⟨46949808335421515493634147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62599744447228687324845529 46949808335421515493634147)
                  ·
                    refine ⟨70424712503132273240451221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46949808335421515493634147 70424712503132273240451221)
                    ·
                      refine ⟨3301158398584325308146151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70424712503132273240451221 3301158398584325308146151)
                      ·
                        rfl

theorem cell23_6428983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_6428983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6428983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6428983 prefixEnd_6428983 := by exact prefixLift 6428983
  have htrace : WordTrace (prefixWord ++ tailWord_6428983) baseStart_6428983 baseEnd_6428983 := by
    simpa [prefixWord, tailWord_6428983, baseEnd_6428983] using wordTrace_append hprefix tailTrace_6428983
  have hstable : (prefixWord ++ tailWord_6428983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6428983).length < 2 ^ (prefixWord ++ tailWord_6428983).sum := by decide
  have hdescent : baseEnd_6428983 < baseStart_6428983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6428983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429022 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6429022 : Nat := 118140960795 + 6429022 * 2 ^ 59
def prefixEnd_6429022 : Nat := 4983230072969 + 3 ^ 40 * 6429022 * 2
def baseEnd_6429022 : Nat := 366797602703316739506497

theorem tailTrace_6429022 : CollatzResearch.WordTrace tailWord_6429022 prefixEnd_6429022 366797602703316739506497 := by
  unfold tailWord_6429022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310712014344844798412165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156323797409839172258198213 29310712014344844798412165)
  ·
    refine ⟨5495758502689658399702281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29310712014344844798412165 5495758502689658399702281)
    ·
      refine ⟨4121818877017243799776711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495758502689658399702281 4121818877017243799776711)
      ·
        refine ⟨6182728315525865699665067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121818877017243799776711 6182728315525865699665067)
        ·
          refine ⟨9274092473288798549497601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182728315525865699665067 9274092473288798549497601)
          ·
            refine ⟨6955569354966598912123201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9274092473288798549497601 6955569354966598912123201)
            ·
              refine ⟨5216677016224949184092401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955569354966598912123201 5216677016224949184092401)
              ·
                refine ⟨3912507762168711888069301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216677016224949184092401 3912507762168711888069301)
                ·
                  refine ⟨366797602703316739506497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912507762168711888069301 366797602703316739506497)
                  ·
                    rfl

theorem cell23_6429022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6429022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429022 prefixEnd_6429022 := by exact prefixLift 6429022
  have htrace : WordTrace (prefixWord ++ tailWord_6429022) baseStart_6429022 baseEnd_6429022 := by
    simpa [prefixWord, tailWord_6429022, baseEnd_6429022] using wordTrace_append hprefix tailTrace_6429022
  have hstable : (prefixWord ++ tailWord_6429022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429022).length < 2 ^ (prefixWord ++ tailWord_6429022).sum := by decide
  have hdescent : baseEnd_6429022 < baseStart_6429022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429031 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 1, 4]
def baseStart_6429031 : Nat := 118140960795 + 6429031 * 2 ^ 59
def prefixEnd_6429031 : Nat := 4983230072969 + 3 ^ 40 * 6429031 * 2
def baseEnd_6429031 : Nat := 1100394348551913706781977

theorem tailTrace_6429031 : CollatzResearch.WordTrace tailWord_6429031 prefixEnd_6429031 1100394348551913706781977 := by
  unfold tailWord_6429031
  simp only [CollatzResearch.WordTrace]
  refine ⟨234486024371726152924374947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156324016247817435282916631 234486024371726152924374947)
  ·
    refine ⟨351729036557589229386562421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234486024371726152924374947 351729036557589229386562421)
    ·
      refine ⟨32974597177273990254990227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351729036557589229386562421 32974597177273990254990227)
      ·
        refine ⟨49461895765910985382485341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32974597177273990254990227 49461895765910985382485341)
        ·
          refine ⟨18548210912216619518432003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49461895765910985382485341 18548210912216619518432003)
          ·
            refine ⟨27822316368324929277648005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18548210912216619518432003 27822316368324929277648005)
            ·
              refine ⟨5216684319060924239559001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27822316368324929277648005 5216684319060924239559001)
              ·
                refine ⟨3912513239295693179669251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216684319060924239559001 3912513239295693179669251)
                ·
                  refine ⟨5868769858943539769503877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912513239295693179669251 5868769858943539769503877)
                  ·
                    refine ⟨1100394348551913706781977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868769858943539769503877 1100394348551913706781977)
                    ·
                      rfl

theorem cell23_6429031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_6429031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429031 prefixEnd_6429031 := by exact prefixLift 6429031
  have htrace : WordTrace (prefixWord ++ tailWord_6429031) baseStart_6429031 baseEnd_6429031 := by
    simpa [prefixWord, tailWord_6429031, baseEnd_6429031] using wordTrace_append hprefix tailTrace_6429031
  have hstable : (prefixWord ++ tailWord_6429031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429031).length < 2 ^ (prefixWord ++ tailWord_6429031).sum := by decide
  have hdescent : baseEnd_6429031 < baseStart_6429031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429040 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_6429040 : Nat := 118140960795 + 6429040 * 2 ^ 59
def prefixEnd_6429040 : Nat := 4983230072969 + 3 ^ 40 * 6429040 * 2
def baseEnd_6429040 : Nat := 1100395888993877195044463

theorem tailTrace_6429040 : CollatzResearch.WordTrace tailWord_6429040 prefixEnd_6429040 1100395888993877195044463 := by
  unfold tailWord_6429040
  simp only [CollatzResearch.WordTrace]
  refine ⟨117243176314346773730726287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156324235085795698307635049 117243176314346773730726287)
  ·
    refine ⟨175864764471520160596089431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117243176314346773730726287 175864764471520160596089431)
    ·
      refine ⟨263797146707280240894134147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175864764471520160596089431 263797146707280240894134147)
      ·
        refine ⟨395695720060920361341201221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263797146707280240894134147 395695720060920361341201221)
        ·
          refine ⟨74192947511422567751475229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395695720060920361341201221 74192947511422567751475229)
          ·
            refine ⟨27822355316783462906803211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74192947511422567751475229 27822355316783462906803211)
            ·
              refine ⟨41733532975175194360204817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27822355316783462906803211 41733532975175194360204817)
              ·
                refine ⟨31300149731381395770153613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41733532975175194360204817 31300149731381395770153613)
                ·
                  refine ⟨11737556149268023413807605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31300149731381395770153613 11737556149268023413807605)
                  ·
                    refine ⟨1100395888993877195044463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11737556149268023413807605 1100395888993877195044463)
                    ·
                      rfl

theorem cell23_6429040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_6429040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429040 prefixEnd_6429040 := by exact prefixLift 6429040
  have htrace : WordTrace (prefixWord ++ tailWord_6429040) baseStart_6429040 baseEnd_6429040 := by
    simpa [prefixWord, tailWord_6429040, baseEnd_6429040] using wordTrace_append hprefix tailTrace_6429040
  have hstable : (prefixWord ++ tailWord_6429040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429040).length < 2 ^ (prefixWord ++ tailWord_6429040).sum := by decide
  have hdescent : baseEnd_6429040 < baseStart_6429040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429057 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6429057 : Nat := 118140960795 + 6429057 * 2 ^ 59
def prefixEnd_6429057 : Nat := 4983230072969 + 3 ^ 40 * 6429057 * 2
def baseEnd_6429057 : Nat := 1100398798717586006206937

theorem tailTrace_6429057 : CollatzResearch.WordTrace tailWord_6429057 prefixEnd_6429057 1100398798717586006206937 := by
  unfold tailWord_6429057
  simp only [CollatzResearch.WordTrace]
  refine ⟨234486972669631959364821425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156324648446421306243214283 234486972669631959364821425)
  ·
    refine ⟨175865229502223969523616069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234486972669631959364821425 175865229502223969523616069)
    ·
      refine ⟨32974730531666994285678013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175865229502223969523616069 32974730531666994285678013)
      ·
        refine ⟨12365523949375122857129255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32974730531666994285678013 12365523949375122857129255)
        ·
          refine ⟨18548285924062684285693883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12365523949375122857129255 18548285924062684285693883)
          ·
            refine ⟨27822428886094026428540825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18548285924062684285693883 27822428886094026428540825)
            ·
              refine ⟨20866821664570519821405619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27822428886094026428540825 20866821664570519821405619)
              ·
                refine ⟨31300232496855779732108429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20866821664570519821405619 31300232496855779732108429)
                ·
                  refine ⟨11737587186320917399540661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31300232496855779732108429 11737587186320917399540661)
                  ·
                    refine ⟨1100398798717586006206937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11737587186320917399540661 1100398798717586006206937)
                    ·
                      rfl

theorem cell23_6429057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6429057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429057 prefixEnd_6429057 := by exact prefixLift 6429057
  have htrace : WordTrace (prefixWord ++ tailWord_6429057) baseStart_6429057 baseEnd_6429057 := by
    simpa [prefixWord, tailWord_6429057, baseEnd_6429057] using wordTrace_append hprefix tailTrace_6429057
  have hstable : (prefixWord ++ tailWord_6429057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429057).length < 2 ^ (prefixWord ++ tailWord_6429057).sum := by decide
  have hdescent : baseEnd_6429057 < baseStart_6429057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429058 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6429058 : Nat := 118140960795 + 6429058 * 2 ^ 59
def prefixEnd_6429058 : Nat := 4983230072969 + 3 ^ 40 * 6429058 * 2
def baseEnd_6429058 : Nat := 3301196909633412514708307

theorem tailTrace_6429058 : CollatzResearch.WordTrace tailWord_6429058 prefixEnd_6429058 3301196909633412514708307 := by
  unfold tailWord_6429058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58621752285657084133901957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156324672761752224357071885 58621752285657084133901957)
  ·
    refine ⟨10991578553560703275106617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58621752285657084133901957 10991578553560703275106617)
    ·
      refine ⟨8243683915170527456329963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991578553560703275106617 8243683915170527456329963)
      ·
        refine ⟨12365525872755791184494945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243683915170527456329963 12365525872755791184494945)
        ·
          refine ⟨9274144404566843388371209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12365525872755791184494945 9274144404566843388371209)
          ·
            refine ⟨6955608303425132541278407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9274144404566843388371209 6955608303425132541278407)
            ·
              refine ⟨10433412455137698811917611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955608303425132541278407 10433412455137698811917611)
              ·
                refine ⟨15650118682706548217876417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10433412455137698811917611 15650118682706548217876417)
                ·
                  refine ⟨11737589012029911163407313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15650118682706548217876417 11737589012029911163407313)
                  ·
                    refine ⟨8803191759022433372555485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11737589012029911163407313 8803191759022433372555485)
                    ·
                      refine ⟨3301196909633412514708307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803191759022433372555485 3301196909633412514708307)
                      ·
                        rfl

theorem cell23_6429058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6429058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429058 prefixEnd_6429058 := by exact prefixLift 6429058
  have htrace : WordTrace (prefixWord ++ tailWord_6429058) baseStart_6429058 baseEnd_6429058 := by
    simpa [prefixWord, tailWord_6429058, baseEnd_6429058] using wordTrace_append hprefix tailTrace_6429058
  have hstable : (prefixWord ++ tailWord_6429058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429058).length < 2 ^ (prefixWord ++ tailWord_6429058).sum := by decide
  have hdescent : baseEnd_6429058 < baseStart_6429058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429087 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 4, 4]
def baseStart_6429087 : Nat := 118140960795 + 6429087 * 2 ^ 59
def prefixEnd_6429087 : Nat := 4983230072969 + 3 ^ 40 * 6429087 * 2
def baseEnd_6429087 : Nat := 1100403933524130967081891

theorem tailTrace_6429087 : CollatzResearch.WordTrace tailWord_6429087 prefixEnd_6429087 1100403933524130967081891 := by
  unfold tailWord_6429087
  simp only [CollatzResearch.WordTrace]
  refine ⟨234488066859523274488413515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156325377906348849658942343 234488066859523274488413515)
  ·
    refine ⟨351732100289284911732620273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234488066859523274488413515 351732100289284911732620273)
    ·
      refine ⟨263799075216963683799465205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351732100289284911732620273 263799075216963683799465205)
      ·
        refine ⟨24731163301590345356199863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263799075216963683799465205 24731163301590345356199863)
        ·
          refine ⟨37096744952385518034299795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24731163301590345356199863 37096744952385518034299795)
          ·
            refine ⟨55645117428578277051449693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37096744952385518034299795 55645117428578277051449693)
            ·
              refine ⟨20866919035716853894293635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55645117428578277051449693 20866919035716853894293635)
              ·
                refine ⟨31300378553575280841440453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20866919035716853894293635 31300378553575280841440453)
                ·
                  refine ⟨5868820978795365157770085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31300378553575280841440453 5868820978795365157770085)
                  ·
                    refine ⟨1100403933524130967081891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868820978795365157770085 1100403933524130967081891)
                    ·
                      rfl

theorem cell23_6429087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_6429087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429087 prefixEnd_6429087 := by exact prefixLift 6429087
  have htrace : WordTrace (prefixWord ++ tailWord_6429087) baseStart_6429087 baseEnd_6429087 := by
    simpa [prefixWord, tailWord_6429087, baseEnd_6429087] using wordTrace_append hprefix tailTrace_6429087
  have hstable : (prefixWord ++ tailWord_6429087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429087).length < 2 ^ (prefixWord ++ tailWord_6429087).sum := by decide
  have hdescent : baseEnd_6429087 < baseStart_6429087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429108 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6429108 : Nat := 118140960795 + 6429108 * 2 ^ 59
def prefixEnd_6429108 : Nat := 4983230072969 + 3 ^ 40 * 6429108 * 2
def baseEnd_6429108 : Nat := 1100407527888712439694359

theorem tailTrace_6429108 : CollatzResearch.WordTrace tailWord_6429108 prefixEnd_6429108 1100407527888712439694359 := by
  unfold tailWord_6429108
  simp only [CollatzResearch.WordTrace]
  refine ⟨117244416396223597537463989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156325888528298130049951985 117244416396223597537463989)
  ·
    refine ⟨10991664037145962269137249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117244416396223597537463989 10991664037145962269137249)
    ·
      refine ⟨8243748027859471701852937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991664037145962269137249 8243748027859471701852937)
      ·
        refine ⟨6182811020894603776389703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243748027859471701852937 6182811020894603776389703)
        ·
          refine ⟨9274216531341905664584555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182811020894603776389703 9274216531341905664584555)
          ·
            refine ⟨13911324797012858496876833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274216531341905664584555 13911324797012858496876833)
            ·
              refine ⟨10433493597759643872657625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13911324797012858496876833 10433493597759643872657625)
              ·
                refine ⟨7825120198319732904493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433493597759643872657625 7825120198319732904493219)
                ·
                  refine ⟨11737680297479599356739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825120198319732904493219 11737680297479599356739829)
                  ·
                    refine ⟨1100407527888712439694359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11737680297479599356739829 1100407527888712439694359)
                    ·
                      rfl

theorem cell23_6429108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6429108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429108 prefixEnd_6429108 := by exact prefixLift 6429108
  have htrace : WordTrace (prefixWord ++ tailWord_6429108) baseStart_6429108 baseEnd_6429108 := by
    simpa [prefixWord, tailWord_6429108, baseEnd_6429108] using wordTrace_append hprefix tailTrace_6429108
  have hstable : (prefixWord ++ tailWord_6429108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429108).length < 2 ^ (prefixWord ++ tailWord_6429108).sum := by decide
  have hdescent : baseEnd_6429108 < baseStart_6429108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429117 : List Nat := [1, 4, 1, 2, 2, 2, 4, 7]
def baseStart_6429117 : Nat := 118140960795 + 6429117 * 2 ^ 59
def prefixEnd_6429117 : Nat := 4983230072969 + 3 ^ 40 * 6429117 * 2
def baseEnd_6429117 : Nat := 122267674258963991995205

theorem tailTrace_6429117 : CollatzResearch.WordTrace tailWord_6429117 prefixEnd_6429117 122267674258963991995205 := by
  unfold tailWord_6429117
  simp only [CollatzResearch.WordTrace]
  refine ⟨234489161049414589612005605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156326107366276393074670403 234489161049414589612005605)
  ·
    refine ⟨43966717696765235552251051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234489161049414589612005605 43966717696765235552251051)
    ·
      refine ⟨65950076545147853328376577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43966717696765235552251051 65950076545147853328376577)
      ·
        refine ⟨49462557408860889996282433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65950076545147853328376577 49462557408860889996282433)
        ·
          refine ⟨37096918056645667497211825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49462557408860889996282433 37096918056645667497211825)
          ·
            refine ⟨27822688542484250622908869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37096918056645667497211825 27822688542484250622908869)
            ·
              refine ⟨5216754101715796991795413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27822688542484250622908869 5216754101715796991795413)
              ·
                refine ⟨122267674258963991995205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5216754101715796991795413 122267674258963991995205)
                ·
                  rfl

theorem cell23_6429117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 7].length) (baseStart_6429117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429117 prefixEnd_6429117 := by exact prefixLift 6429117
  have htrace : WordTrace (prefixWord ++ tailWord_6429117) baseStart_6429117 baseEnd_6429117 := by
    simpa [prefixWord, tailWord_6429117, baseEnd_6429117] using wordTrace_append hprefix tailTrace_6429117
  have hstable : (prefixWord ++ tailWord_6429117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429117).length < 2 ^ (prefixWord ++ tailWord_6429117).sum := by decide
  have hdescent : baseEnd_6429117 < baseStart_6429117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429128 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_6429128 : Nat := 118140960795 + 6429128 * 2 ^ 59
def prefixEnd_6429128 : Nat := 4983230072969 + 3 ^ 40 * 6429128 * 2
def baseEnd_6429128 : Nat := 3301232853279227240832985

theorem tailTrace_6429128 : CollatzResearch.WordTrace tailWord_6429128 prefixEnd_6429128 3301232853279227240832985 := by
  unfold tailWord_6429128
  simp only [CollatzResearch.WordTrace]
  refine ⟨117244781126187369245328019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156326374834916492327104025 117244781126187369245328019)
  ·
    refine ⟨175867171689281053867992029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117244781126187369245328019 175867171689281053867992029)
    ·
      refine ⟨65950189383480395200497011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175867171689281053867992029 65950189383480395200497011)
      ·
        refine ⟨98925284075220592800745517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65950189383480395200497011 98925284075220592800745517)
        ·
          refine ⟨37096981528207722300279569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98925284075220592800745517 37096981528207722300279569)
          ·
            refine ⟨27822736146155791725209677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37096981528207722300279569 27822736146155791725209677)
            ·
              refine ⟨10433526054808421896953629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27822736146155791725209677 10433526054808421896953629)
              ·
                refine ⟨3912572270553158211357611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10433526054808421896953629 3912572270553158211357611)
                ·
                  refine ⟨5868858405829737317036417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912572270553158211357611 5868858405829737317036417)
                  ·
                    refine ⟨4401643804372302987777313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868858405829737317036417 4401643804372302987777313)
                    ·
                      refine ⟨3301232853279227240832985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401643804372302987777313 3301232853279227240832985)
                      ·
                        rfl

theorem cell23_6429128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_6429128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429128 prefixEnd_6429128 := by exact prefixLift 6429128
  have htrace : WordTrace (prefixWord ++ tailWord_6429128) baseStart_6429128 baseEnd_6429128 := by
    simpa [prefixWord, tailWord_6429128, baseEnd_6429128] using wordTrace_append hprefix tailTrace_6429128
  have hstable : (prefixWord ++ tailWord_6429128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429128).length < 2 ^ (prefixWord ++ tailWord_6429128).sum := by decide
  have hdescent : baseEnd_6429128 < baseStart_6429128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429144 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_6429144 : Nat := 118140960795 + 6429144 * 2 ^ 59
def prefixEnd_6429144 : Nat := 4983230072969 + 3 ^ 40 * 6429144 * 2
def baseEnd_6429144 : Nat := 3301241068969699178232911

theorem tailTrace_6429144 : CollatzResearch.WordTrace tailWord_6429144 prefixEnd_6429144 3301241068969699178232911 := by
  unfold tailWord_6429144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117245072910158386611619243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156326763880211182148825657 117245072910158386611619243)
  ·
    refine ⟨175867609365237579917428865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117245072910158386611619243 175867609365237579917428865)
    ·
      refine ⟨131900707023928184938071649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175867609365237579917428865 131900707023928184938071649)
      ·
        refine ⟨98925530267946138703553737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131900707023928184938071649 98925530267946138703553737)
        ·
          refine ⟨74194147700959604027665303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98925530267946138703553737 74194147700959604027665303)
          ·
            refine ⟨111291221551439406041497955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74194147700959604027665303 111291221551439406041497955)
            ·
              refine ⟨166936832327159109062246933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111291221551439406041497955 166936832327159109062246933)
              ·
                refine ⟨7825164015335583237292825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166936832327159109062246933 7825164015335583237292825)
                ·
                  refine ⟨5868873011501687427969619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7825164015335583237292825 5868873011501687427969619)
                  ·
                    refine ⟨8803309517252531141954429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868873011501687427969619 8803309517252531141954429)
                    ·
                      refine ⟨3301241068969699178232911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803309517252531141954429 3301241068969699178232911)
                      ·
                        rfl

theorem cell23_6429144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_6429144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429144 prefixEnd_6429144 := by exact prefixLift 6429144
  have htrace : WordTrace (prefixWord ++ tailWord_6429144) baseStart_6429144 baseEnd_6429144 := by
    simpa [prefixWord, tailWord_6429144, baseEnd_6429144] using wordTrace_append hprefix tailTrace_6429144
  have hstable : (prefixWord ++ tailWord_6429144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429144).length < 2 ^ (prefixWord ++ tailWord_6429144).sum := by decide
  have hdescent : baseEnd_6429144 < baseStart_6429144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429224 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 7]
def baseStart_6429224 : Nat := 118140960795 + 6429224 * 2 ^ 59
def prefixEnd_6429224 : Nat := 4983230072969 + 3 ^ 40 * 6429224 * 2
def baseEnd_6429224 : Nat := 366809127491339873914727

theorem tailTrace_6429224 : CollatzResearch.WordTrace tailWord_6429224 prefixEnd_6429224 366809127491339873914727 := by
  unfold tailWord_6429224
  simp only [CollatzResearch.WordTrace]
  refine ⟨117246531830013473443075363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156328709106684631257433817 117246531830013473443075363)
  ·
    refine ⟨175869797745020210164613045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117246531830013473443075363 175869797745020210164613045)
    ·
      refine ⟨16487793538595644702932473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175869797745020210164613045 16487793538595644702932473)
      ·
        refine ⟨12365845153946733527199355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16487793538595644702932473 12365845153946733527199355)
        ·
          refine ⟨18548767730920100290799033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12365845153946733527199355 18548767730920100290799033)
          ·
            refine ⟨13911575798190075218099275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18548767730920100290799033 13911575798190075218099275)
            ·
              refine ⟨20867363697285112827148913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13911575798190075218099275 20867363697285112827148913)
              ·
                refine ⟨15650522772963834620361685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20867363697285112827148913 15650522772963834620361685)
                ·
                  refine ⟨366809127491339873914727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15650522772963834620361685 366809127491339873914727)
                  ·
                    rfl

theorem cell23_6429224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_6429224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429224 prefixEnd_6429224 := by exact prefixLift 6429224
  have htrace : WordTrace (prefixWord ++ tailWord_6429224) baseStart_6429224 baseEnd_6429224 := by
    simpa [prefixWord, tailWord_6429224, baseEnd_6429224] using wordTrace_append hprefix tailTrace_6429224
  have hstable : (prefixWord ++ tailWord_6429224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429224).length < 2 ^ (prefixWord ++ tailWord_6429224).sum := by decide
  have hdescent : baseEnd_6429224 < baseStart_6429224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429237 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6429237 : Nat := 118140960795 + 6429237 * 2 ^ 59
def prefixEnd_6429237 : Nat := 4983230072969 + 3 ^ 40 * 6429237 * 2
def baseEnd_6429237 : Nat := 1100429607556855771456661

theorem tailTrace_6429237 : CollatzResearch.WordTrace tailWord_6429237 prefixEnd_6429237 1100429607556855771456661 := by
  unfold tailWord_6429237
  simp only [CollatzResearch.WordTrace]
  refine ⟨234493537808979850106373965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156329025205986566737582643 234493537808979850106373965)
  ·
    refine ⟨87935076678367443789890237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234493537808979850106373965 87935076678367443789890237)
    ·
      refine ⟨32975653754387791421208839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87935076678367443789890237 32975653754387791421208839)
      ·
        refine ⟨49463480631581687131813259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32975653754387791421208839 49463480631581687131813259)
        ·
          refine ⟨74195220947372530697719889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49463480631581687131813259 74195220947372530697719889)
          ·
            refine ⟨55646415710529398023289917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74195220947372530697719889 55646415710529398023289917)
            ·
              refine ⟨20867405891448524258733719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55646415710529398023289917 20867405891448524258733719)
              ·
                refine ⟨31301108837172786388100579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20867405891448524258733719 31301108837172786388100579)
                ·
                  refine ⟨46951663255759179582150869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31301108837172786388100579 46951663255759179582150869)
                  ·
                    refine ⟨1100429607556855771456661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46951663255759179582150869 1100429607556855771456661)
                    ·
                      rfl

theorem cell23_6429237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6429237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429237 prefixEnd_6429237 := by exact prefixLift 6429237
  have htrace : WordTrace (prefixWord ++ tailWord_6429237) baseStart_6429237 baseEnd_6429237 := by
    simpa [prefixWord, tailWord_6429237, baseEnd_6429237] using wordTrace_append hprefix tailTrace_6429237
  have hstable : (prefixWord ++ tailWord_6429237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429237).length < 2 ^ (prefixWord ++ tailWord_6429237).sum := by decide
  have hdescent : baseEnd_6429237 < baseStart_6429237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429252 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6429252 : Nat := 118140960795 + 6429252 * 2 ^ 59
def prefixEnd_6429252 : Nat := 4983230072969 + 3 ^ 40 * 6429252 * 2
def baseEnd_6429252 : Nat := 3301296524880384755682415

theorem tailTrace_6429252 : CollatzResearch.WordTrace tailWord_6429252 prefixEnd_6429252 3301296524880384755682415 := by
  unfold tailWord_6429252
  simp only [CollatzResearch.WordTrace]
  refine ⟨117247042451962753834085005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156329389935950338445446673 117247042451962753834085005)
  ·
    refine ⟨43967640919486032687781877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117247042451962753834085005 43967640919486032687781877)
    ·
      refine ⟨4121966336201815564479551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43967640919486032687781877 4121966336201815564479551)
      ·
        refine ⟨6182949504302723346719327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121966336201815564479551 6182949504302723346719327)
        ·
          refine ⟨9274424256454085020078991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182949504302723346719327 9274424256454085020078991)
          ·
            refine ⟨13911636384681127530118487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274424256454085020078991 13911636384681127530118487)
            ·
              refine ⟨20867454577021691295177731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13911636384681127530118487 20867454577021691295177731)
              ·
                refine ⟨31301181865532536942766597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20867454577021691295177731 31301181865532536942766597)
                ·
                  refine ⟨5868971599787350676768737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31301181865532536942766597 5868971599787350676768737)
                  ·
                    refine ⟨4401728699840513007576553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5868971599787350676768737 4401728699840513007576553)
                    ·
                      refine ⟨3301296524880384755682415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4401728699840513007576553 3301296524880384755682415)
                      ·
                        rfl

theorem cell23_6429252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6429252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429252 prefixEnd_6429252 := by exact prefixLift 6429252
  have htrace : WordTrace (prefixWord ++ tailWord_6429252) baseStart_6429252 baseEnd_6429252 := by
    simpa [prefixWord, tailWord_6429252, baseEnd_6429252] using wordTrace_append hprefix tailTrace_6429252
  have hstable : (prefixWord ++ tailWord_6429252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429252).length < 2 ^ (prefixWord ++ tailWord_6429252).sum := by decide
  have hdescent : baseEnd_6429252 < baseStart_6429252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429284 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_6429284 : Nat := 118140960795 + 6429284 * 2 ^ 59
def prefixEnd_6429284 : Nat := 4983230072969 + 3 ^ 40 * 6429284 * 2
def baseEnd_6429284 : Nat := 1100437652087109543494089

theorem tailTrace_6429284 : CollatzResearch.WordTrace tailWord_6429284 prefixEnd_6429284 1100437652087109543494089 := by
  unfold tailWord_6429284
  simp only [CollatzResearch.WordTrace]
  refine ⟨117247626019904788566667453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156330168026539718088889937 117247626019904788566667453)
  ·
    refine ⟨43967859757464295712500295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117247626019904788566667453 43967859757464295712500295)
    ·
      refine ⟨65951789636196443568750443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43967859757464295712500295 65951789636196443568750443)
      ·
        refine ⟨98927684454294665353125665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65951789636196443568750443 98927684454294665353125665)
        ·
          refine ⟨74195763340720999014844249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98927684454294665353125665 74195763340720999014844249)
          ·
            refine ⟨55646822505540749261133187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74195763340720999014844249 55646822505540749261133187)
            ·
              refine ⟨83470233758311123891699781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55646822505540749261133187 83470233758311123891699781)
              ·
                refine ⟨15650668829683335729693709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83470233758311123891699781 15650668829683335729693709)
                ·
                  refine ⟨5869000811131250898635141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15650668829683335729693709 5869000811131250898635141)
                  ·
                    refine ⟨1100437652087109543494089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5869000811131250898635141 1100437652087109543494089)
                    ·
                      rfl

theorem cell23_6429284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_6429284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429284 prefixEnd_6429284 := by exact prefixLift 6429284
  have htrace : WordTrace (prefixWord ++ tailWord_6429284) baseStart_6429284 baseEnd_6429284 := by
    simpa [prefixWord, tailWord_6429284, baseEnd_6429284] using wordTrace_append hprefix tailTrace_6429284
  have hstable : (prefixWord ++ tailWord_6429284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429284).length < 2 ^ (prefixWord ++ tailWord_6429284).sum := by decide
  have hdescent : baseEnd_6429284 < baseStart_6429284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429287 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6429287 : Nat := 118140960795 + 6429287 * 2 ^ 59
def prefixEnd_6429287 : Nat := 4983230072969 + 3 ^ 40 * 6429287 * 2
def baseEnd_6429287 : Nat := 3301314496703292118744753

theorem tailTrace_6429287 : CollatzResearch.WordTrace tailWord_6429287 prefixEnd_6429287 3301314496703292118744753 := by
  unfold tailWord_6429287
  simp only [CollatzResearch.WordTrace]
  refine ⟨234495361458798708645694115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156330240972532472430462743 234495361458798708645694115)
  ·
    refine ⟨351743042188198062968541173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234495361458798708645694115 351743042188198062968541173)
    ·
      refine ⟨32975910205143568403300735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351743042188198062968541173 32975910205143568403300735)
      ·
        refine ⟨49463865307715352604951103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32975910205143568403300735 49463865307715352604951103)
        ·
          refine ⟨74195797961573028907426655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49463865307715352604951103 74195797961573028907426655)
          ·
            refine ⟨111293696942359543361139983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74195797961573028907426655 111293696942359543361139983)
            ·
              refine ⟨166940545413539315041709975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111293696942359543361139983 166940545413539315041709975)
              ·
                refine ⟨250410818120308972562564963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166940545413539315041709975 250410818120308972562564963)
                ·
                  refine ⟨375616227180463458843847445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250410818120308972562564963 375616227180463458843847445)
                  ·
                    refine ⟨17607010649084224633305349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 375616227180463458843847445 17607010649084224633305349)
                    ·
                      refine ⟨3301314496703292118744753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17607010649084224633305349 3301314496703292118744753)
                      ·
                        rfl

theorem cell23_6429287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6429287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429287 prefixEnd_6429287 := by exact prefixLift 6429287
  have htrace : WordTrace (prefixWord ++ tailWord_6429287) baseStart_6429287 baseEnd_6429287 := by
    simpa [prefixWord, tailWord_6429287, baseEnd_6429287] using wordTrace_append hprefix tailTrace_6429287
  have hstable : (prefixWord ++ tailWord_6429287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429287).length < 2 ^ (prefixWord ++ tailWord_6429287).sum := by decide
  have hdescent : baseEnd_6429287 < baseStart_6429287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 5, 5]
def baseStart_6429327 : Nat := 118140960795 + 6429327 * 2 ^ 59
def prefixEnd_6429327 : Nat := 4983230072969 + 3 ^ 40 * 6429327 * 2
def baseEnd_6429327 : Nat := 1100445011976490654081523

theorem tailTrace_6429327 : CollatzResearch.WordTrace tailWord_6429327 prefixEnd_6429327 1100445011976490654081523 := by
  unfold tailWord_6429327
  simp only [CollatzResearch.WordTrace]
  refine ⟨234496820378653795477150235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156331213585769196984766823 234496820378653795477150235)
  ·
    refine ⟨351745230567980693215725353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234496820378653795477150235 351745230567980693215725353)
    ·
      refine ⟨263808922925985519911794015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351745230567980693215725353 263808922925985519911794015)
      ·
        refine ⟨395713384388978279867691023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263808922925985519911794015 395713384388978279867691023)
        ·
          refine ⟨593570076583467419801536535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395713384388978279867691023 593570076583467419801536535)
          ·
            refine ⟨890355114875201129702304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593570076583467419801536535 890355114875201129702304803)
            ·
              refine ⟨1335532672312801694553457205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890355114875201129702304803 1335532672312801694553457205)
              ·
                refine ⟨125206188029325158864386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335532672312801694553457205 125206188029325158864386613)
                ·
                  refine ⟨11738080127749233643536245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125206188029325158864386613 11738080127749233643536245)
                  ·
                    refine ⟨1100445011976490654081523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11738080127749233643536245 1100445011976490654081523)
                    ·
                      rfl

theorem cell23_6429327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_6429327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429327 prefixEnd_6429327 := by exact prefixLift 6429327
  have htrace : WordTrace (prefixWord ++ tailWord_6429327) baseStart_6429327 baseEnd_6429327 := by
    simpa [prefixWord, tailWord_6429327, baseEnd_6429327] using wordTrace_append hprefix tailTrace_6429327
  have hstable : (prefixWord ++ tailWord_6429327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429327).length < 2 ^ (prefixWord ++ tailWord_6429327).sum := by decide
  have hdescent : baseEnd_6429327 < baseStart_6429327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429341 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_6429341 : Nat := 118140960795 + 6429341 * 2 ^ 59
def prefixEnd_6429341 : Nat := 4983230072969 + 3 ^ 40 * 6429341 * 2
def baseEnd_6429341 : Nat := 3301342224658634907469505

theorem tailTrace_6429341 : CollatzResearch.WordTrace tailWord_6429341 prefixEnd_6429341 3301342224658634907469505 := by
  unfold tailWord_6429341
  simp only [CollatzResearch.WordTrace]
  refine ⟨234497331000603075868159877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156331554000402050578773251 234497331000603075868159877)
  ·
    refine ⟨43968249562613076725279977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234497331000603075868159877 43968249562613076725279977)
    ·
      refine ⟨32976187171959807543959983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43968249562613076725279977 32976187171959807543959983)
      ·
        refine ⟨49464280757939711315939975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32976187171959807543959983 49464280757939711315939975)
        ·
          refine ⟨74196421136909566973909963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49464280757939711315939975 74196421136909566973909963)
          ·
            refine ⟨111294631705364350460864945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74196421136909566973909963 111294631705364350460864945)
            ·
              refine ⟨83470973779023262845648709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111294631705364350460864945 83470973779023262845648709)
              ·
                refine ⟨15650807583566861783559133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83470973779023262845648709 15650807583566861783559133)
                ·
                  refine ⟨5869052843837573168834675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15650807583566861783559133 5869052843837573168834675)
                  ·
                    refine ⟨8803579265756359753252013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5869052843837573168834675 8803579265756359753252013)
                    ·
                      refine ⟨3301342224658634907469505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803579265756359753252013 3301342224658634907469505)
                      ·
                        rfl

theorem cell23_6429341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_6429341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429341 prefixEnd_6429341 := by exact prefixLift 6429341
  have htrace : WordTrace (prefixWord ++ tailWord_6429341) baseStart_6429341 baseEnd_6429341 := by
    simpa [prefixWord, tailWord_6429341, baseEnd_6429341] using wordTrace_append hprefix tailTrace_6429341
  have hstable : (prefixWord ++ tailWord_6429341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429341).length < 2 ^ (prefixWord ++ tailWord_6429341).sum := by decide
  have hdescent : baseEnd_6429341 < baseStart_6429341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429374 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6429374 : Nat := 118140960795 + 6429374 * 2 ^ 59
def prefixEnd_6429374 : Nat := 4983230072969 + 3 ^ 40 * 6429374 * 2
def baseEnd_6429374 : Nat := 1100453056506744426118951

theorem tailTrace_6429374 : CollatzResearch.WordTrace tailWord_6429374 prefixEnd_6429374 1100453056506744426118951 := by
  unfold tailWord_6429374
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312316826185440313013897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156332356406322348336074117 29312316826185440313013897)
  ·
    refine ⟨21984237619639080234760423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29312316826185440313013897 21984237619639080234760423)
    ·
      refine ⟨32976356429458620352140635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984237619639080234760423 32976356429458620352140635)
      ·
        refine ⟨49464534644187930528210953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32976356429458620352140635 49464534644187930528210953)
        ·
          refine ⟨37098400983140947896158215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49464534644187930528210953 37098400983140947896158215)
          ·
            refine ⟨55647601474711421844237323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37098400983140947896158215 55647601474711421844237323)
            ·
              refine ⟨83471402212067132766355985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55647601474711421844237323 83471402212067132766355985)
              ·
                refine ⟨62603551659050349574766989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83471402212067132766355985 62603551659050349574766989)
                ·
                  refine ⟨23476331872143881090537621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62603551659050349574766989 23476331872143881090537621)
                  ·
                    refine ⟨1100453056506744426118951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23476331872143881090537621 1100453056506744426118951)
                    ·
                      rfl

theorem cell23_6429374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6429374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429374 prefixEnd_6429374 := by exact prefixLift 6429374
  have htrace : WordTrace (prefixWord ++ tailWord_6429374) baseStart_6429374 baseEnd_6429374 := by
    simpa [prefixWord, tailWord_6429374, baseEnd_6429374] using wordTrace_append hprefix tailTrace_6429374
  have hstable : (prefixWord ++ tailWord_6429374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429374).length < 2 ^ (prefixWord ++ tailWord_6429374).sum := by decide
  have hdescent : baseEnd_6429374 < baseStart_6429374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429375 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 1, 1, 3]
def baseStart_6429375 : Nat := 118140960795 + 6429375 * 2 ^ 59
def prefixEnd_6429375 : Nat := 4983230072969 + 3 ^ 40 * 6429375 * 2
def baseEnd_6429375 : Nat := 3301359683000887774444349

theorem tailTrace_6429375 : CollatzResearch.WordTrace tailWord_6429375 prefixEnd_6429375 3301359683000887774444349 := by
  unfold tailWord_6429375
  simp only [CollatzResearch.WordTrace]
  refine ⟨234498571082479899674897579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156332380721653266449931719 234498571082479899674897579)
  ·
    refine ⟨351747856623719849512346369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234498571082479899674897579 351747856623719849512346369)
    ·
      refine ⟨263810892467789887134259777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351747856623719849512346369 263810892467789887134259777)
      ·
        refine ⟨197858169350842415350694833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263810892467789887134259777 197858169350842415350694833)
        ·
          refine ⟨148393627013131811513021125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197858169350842415350694833 148393627013131811513021125)
          ·
            refine ⟨27823805064962214658691461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148393627013131811513021125 27823805064962214658691461)
            ·
              refine ⟨5216963449680415248504649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27823805064962214658691461 5216963449680415248504649)
              ·
                refine ⟨3912722587260311436378487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216963449680415248504649 3912722587260311436378487)
                ·
                  refine ⟨5869083880890467154567731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912722587260311436378487 5869083880890467154567731)
                  ·
                    refine ⟨8803625821335700731851597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5869083880890467154567731 8803625821335700731851597)
                    ·
                      refine ⟨3301359683000887774444349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803625821335700731851597 3301359683000887774444349)
                      ·
                        rfl

theorem cell23_6429375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_6429375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429375 prefixEnd_6429375 := by exact prefixLift 6429375
  have htrace : WordTrace (prefixWord ++ tailWord_6429375) baseStart_6429375 baseEnd_6429375 := by
    simpa [prefixWord, tailWord_6429375, baseEnd_6429375] using wordTrace_append hprefix tailTrace_6429375
  have hstable : (prefixWord ++ tailWord_6429375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429375).length < 2 ^ (prefixWord ++ tailWord_6429375).sum := by decide
  have hdescent : baseEnd_6429375 < baseStart_6429375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429401 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_6429401 : Nat := 118140960795 + 6429401 * 2 ^ 59
def prefixEnd_6429401 : Nat := 4983230072969 + 3 ^ 40 * 6429401 * 2
def baseEnd_6429401 : Nat := 3301373033497904672719229

theorem tailTrace_6429401 : CollatzResearch.WordTrace tailWord_6429401 prefixEnd_6429401 3301373033497904672719229 := by
  unfold tailWord_6429401
  simp only [CollatzResearch.WordTrace]
  refine ⟨234499519380385706115344057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156333012920257137410229371 234499519380385706115344057)
  ·
    refine ⟨175874639535289279586508043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234499519380385706115344057 175874639535289279586508043)
    ·
      refine ⟨263811959302933919379762065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175874639535289279586508043 263811959302933919379762065)
      ·
        refine ⟨197858969477200439534821549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263811959302933919379762065 197858969477200439534821549)
        ·
          refine ⟨74197113553950164825558081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197858969477200439534821549 74197113553950164825558081)
          ·
            refine ⟨55647835165462623619168561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74197113553950164825558081 55647835165462623619168561)
            ·
              refine ⟨41735876374096967714376421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55647835165462623619168561 41735876374096967714376421)
              ·
                refine ⟨7825476820143181446445579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41735876374096967714376421 7825476820143181446445579)
                ·
                  refine ⟨11738215230214772169668369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825476820143181446445579 11738215230214772169668369)
                  ·
                    refine ⟨8803661422661079127251277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11738215230214772169668369 8803661422661079127251277)
                    ·
                      refine ⟨3301373033497904672719229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803661422661079127251277 3301373033497904672719229)
                      ·
                        rfl

theorem cell23_6429401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_6429401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429401 prefixEnd_6429401 := by exact prefixLift 6429401
  have htrace : WordTrace (prefixWord ++ tailWord_6429401) baseStart_6429401 baseEnd_6429401 := by
    simpa [prefixWord, tailWord_6429401, baseEnd_6429401] using wordTrace_append hprefix tailTrace_6429401
  have hstable : (prefixWord ++ tailWord_6429401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429401).length < 2 ^ (prefixWord ++ tailWord_6429401).sum := by decide
  have hdescent : baseEnd_6429401 < baseStart_6429401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429411 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6429411 : Nat := 118140960795 + 6429411 * 2 ^ 59
def prefixEnd_6429411 : Nat := 4983230072969 + 3 ^ 40 * 6429411 * 2
def baseEnd_6429411 : Nat := 3301378168304449633594183

theorem tailTrace_6429411 : CollatzResearch.WordTrace tailWord_6429411 prefixEnd_6429411 3301378168304449633594183 := by
  unfold tailWord_6429411
  simp only [CollatzResearch.WordTrace]
  refine ⟨234499884110349477823208087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156333256073566318548805391 234499884110349477823208087)
  ·
    refine ⟨351749826165524216734812131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234499884110349477823208087 351749826165524216734812131)
    ·
      refine ⟨527624739248286325102218197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351749826165524216734812131 527624739248286325102218197)
      ·
        refine ⟨12366204826131710744583239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 527624739248286325102218197 12366204826131710744583239)
        ·
          refine ⟨18549307239197566116874859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366204826131710744583239 18549307239197566116874859)
          ·
            refine ⟨27823960858796349175312289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18549307239197566116874859 27823960858796349175312289)
            ·
              refine ⟨20867970644097261881484217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27823960858796349175312289 20867970644097261881484217)
              ·
                refine ⟨15650977983072946411113163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20867970644097261881484217 15650977983072946411113163)
                ·
                  refine ⟨23476466974609419616669745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15650977983072946411113163 23476466974609419616669745)
                  ·
                    refine ⟨17607350230957064712502309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23476466974609419616669745 17607350230957064712502309)
                    ·
                      refine ⟨3301378168304449633594183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17607350230957064712502309 3301378168304449633594183)
                      ·
                        rfl

theorem cell23_6429411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6429411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429411 prefixEnd_6429411 := by exact prefixLift 6429411
  have htrace : WordTrace (prefixWord ++ tailWord_6429411) baseStart_6429411 baseEnd_6429411 := by
    simpa [prefixWord, tailWord_6429411, baseEnd_6429411] using wordTrace_append hprefix tailTrace_6429411
  have hstable : (prefixWord ++ tailWord_6429411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429411).length < 2 ^ (prefixWord ++ tailWord_6429411).sum := by decide
  have hdescent : baseEnd_6429411 < baseStart_6429411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429448 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_6429448 : Nat := 118140960795 + 6429448 * 2 ^ 59
def prefixEnd_6429448 : Nat := 4983230072969 + 3 ^ 40 * 6429448 * 2
def baseEnd_6429448 : Nat := 3301397167088665988831513

theorem tailTrace_6429448 : CollatzResearch.WordTrace tailWord_6429448 prefixEnd_6429448 3301397167088665988831513 := by
  unfold tailWord_6429448
  simp only [CollatzResearch.WordTrace]
  refine ⟨117250616805607716571152499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156334155740810288761536665 117250616805607716571152499)
  ·
    refine ⟨175875925208411574856728749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117250616805607716571152499 175875925208411574856728749)
    ·
      refine ⟨65953471953154340571273281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175875925208411574856728749 65953471953154340571273281)
      ·
        refine ⟨49465103964865755428454961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65953471953154340571273281 49465103964865755428454961)
        ·
          refine ⟨37098827973649316571341221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49465103964865755428454961 37098827973649316571341221)
          ·
            refine ⟨6956030245059246857126479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37098827973649316571341221 6956030245059246857126479)
            ·
              refine ⟨10434045367588870285689719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956030245059246857126479 10434045367588870285689719)
              ·
                refine ⟨15651068051383305428534579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434045367588870285689719 15651068051383305428534579)
                ·
                  refine ⟨23476602077074958142801869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15651068051383305428534579 23476602077074958142801869)
                  ·
                    refine ⟨8803725778903109303550701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23476602077074958142801869 8803725778903109303550701)
                    ·
                      refine ⟨3301397167088665988831513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8803725778903109303550701 3301397167088665988831513)
                      ·
                        rfl

theorem cell23_6429448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_6429448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429448 prefixEnd_6429448 := by exact prefixLift 6429448
  have htrace : WordTrace (prefixWord ++ tailWord_6429448) baseStart_6429448 baseEnd_6429448 := by
    simpa [prefixWord, tailWord_6429448, baseEnd_6429448] using wordTrace_append hprefix tailTrace_6429448
  have hstable : (prefixWord ++ tailWord_6429448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429448).length < 2 ^ (prefixWord ++ tailWord_6429448).sum := by decide
  have hdescent : baseEnd_6429448 < baseStart_6429448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429541 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_6429541 : Nat := 118140960795 + 6429541 * 2 ^ 59
def prefixEnd_6429541 : Nat := 4983230072969 + 3 ^ 40 * 6429541 * 2
def baseEnd_6429541 : Nat := 1100481640263178041656195

theorem tailTrace_6429541 : CollatzResearch.WordTrace tailWord_6429541 prefixEnd_6429541 1100481640263178041656195 := by
  unfold tailWord_6429541
  simp only [CollatzResearch.WordTrace]
  refine ⟨234504625599878510025440477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156336417066585673350293651 234504625599878510025440477)
  ·
    refine ⟨87939234599954441259540179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234504625599878510025440477 87939234599954441259540179)
    ·
      refine ⟨131908851899931661889310269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87939234599954441259540179 131908851899931661889310269)
      ·
        refine ⟨49465819462474373208491351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131908851899931661889310269 49465819462474373208491351)
        ·
          refine ⟨74198729193711559812737027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49465819462474373208491351 74198729193711559812737027)
          ·
            refine ⟨111298093790567339719105541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74198729193711559812737027 111298093790567339719105541)
            ·
              refine ⟨20868392585731376197332289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111298093790567339719105541 20868392585731376197332289)
              ·
                refine ⟨15651294439298532147999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20868392585731376197332289 15651294439298532147999217)
                ·
                  refine ⟨11738470829473899110999413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15651294439298532147999217 11738470829473899110999413)
                  ·
                    refine ⟨1100481640263178041656195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11738470829473899110999413 1100481640263178041656195)
                    ·
                      rfl

theorem cell23_6429541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_6429541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429541 prefixEnd_6429541 := by exact prefixLift 6429541
  have htrace : WordTrace (prefixWord ++ tailWord_6429541) baseStart_6429541 baseEnd_6429541 := by
    simpa [prefixWord, tailWord_6429541, baseEnd_6429541] using wordTrace_append hprefix tailTrace_6429541
  have hstable : (prefixWord ++ tailWord_6429541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429541).length < 2 ^ (prefixWord ++ tailWord_6429541).sum := by decide
  have hdescent : baseEnd_6429541 < baseStart_6429541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429578 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6429578 : Nat := 118140960795 + 6429578 * 2 ^ 59
def prefixEnd_6429578 : Nat := 4983230072969 + 3 ^ 40 * 6429578 * 2
def baseEnd_6429578 : Nat := 3301463919573750480205915

theorem tailTrace_6429578 : CollatzResearch.WordTrace tailWord_6429578 prefixEnd_6429578 3301463919573750480205915 := by
  unfold tailWord_6429578
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626493775186116336134347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156337316733829643563024925 58626493775186116336134347)
  ·
    refine ⟨87939740662779174504201521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58626493775186116336134347 87939740662779174504201521)
    ·
      refine ⟨65954805497084380878151141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87939740662779174504201521 65954805497084380878151141)
      ·
        refine ⟨12366526030703321414653339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65954805497084380878151141 12366526030703321414653339)
        ·
          refine ⟨18549789046054982121980009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366526030703321414653339 18549789046054982121980009)
          ·
            refine ⟨13912341784541236591485007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18549789046054982121980009 13912341784541236591485007)
            ·
              refine ⟨20868512676811854887227511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13912341784541236591485007 20868512676811854887227511)
              ·
                refine ⟨31302769015217782330841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20868512676811854887227511 31302769015217782330841267)
                ·
                  refine ⟨46954153522826673496261901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31302769015217782330841267 46954153522826673496261901)
                  ·
                    refine ⟨17607807571060002561098213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46954153522826673496261901 17607807571060002561098213)
                    ·
                      refine ⟨3301463919573750480205915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17607807571060002561098213 3301463919573750480205915)
                      ·
                        rfl

theorem cell23_6429578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6429578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429578 prefixEnd_6429578 := by exact prefixLift 6429578
  have htrace : WordTrace (prefixWord ++ tailWord_6429578) baseStart_6429578 baseEnd_6429578 := by
    simpa [prefixWord, tailWord_6429578, baseEnd_6429578] using wordTrace_append hprefix tailTrace_6429578
  have hstable : (prefixWord ++ tailWord_6429578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429578).length < 2 ^ (prefixWord ++ tailWord_6429578).sum := by decide
  have hdescent : baseEnd_6429578 < baseStart_6429578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429588 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6429588 : Nat := 118140960795 + 6429588 * 2 ^ 59
def prefixEnd_6429588 : Nat := 4983230072969 + 3 ^ 40 * 6429588 * 2
def baseEnd_6429588 : Nat := 1100489684793431813693623

theorem tailTrace_6429588 : CollatzResearch.WordTrace tailWord_6429588 prefixEnd_6429588 1100489684793431813693623 := by
  unfold tailWord_6429588
  simp only [CollatzResearch.WordTrace]
  refine ⟨117253169915354118526200709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156337559887138824701600945 117253169915354118526200709)
  ·
    refine ⟨21984969359128897223662633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117253169915354118526200709 21984969359128897223662633)
    ·
      refine ⟨16488727019346672917746975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21984969359128897223662633 16488727019346672917746975)
      ·
        refine ⟨24733090529020009376620463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16488727019346672917746975 24733090529020009376620463)
        ·
          refine ⟨37099635793530014064930695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24733090529020009376620463 37099635793530014064930695)
          ·
            refine ⟨55649453690295021097396043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37099635793530014064930695 55649453690295021097396043)
            ·
              refine ⟨83474180535442531646094065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55649453690295021097396043 83474180535442531646094065)
              ·
                refine ⟨62605635401581898734570549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83474180535442531646094065 62605635401581898734570549)
                ·
                  refine ⟨5869278318898303006365989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62605635401581898734570549 5869278318898303006365989)
                  ·
                    refine ⟨1100489684793431813693623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5869278318898303006365989 1100489684793431813693623)
                    ·
                      rfl

theorem cell23_6429588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6429588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429588 prefixEnd_6429588 := by exact prefixLift 6429588
  have htrace : WordTrace (prefixWord ++ tailWord_6429588) baseStart_6429588 baseEnd_6429588 := by
    simpa [prefixWord, tailWord_6429588, baseEnd_6429588] using wordTrace_append hprefix tailTrace_6429588
  have hstable : (prefixWord ++ tailWord_6429588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429588).length < 2 ^ (prefixWord ++ tailWord_6429588).sum := by decide
  have hdescent : baseEnd_6429588 < baseStart_6429588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429621 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6429621 : Nat := 118140960795 + 6429621 * 2 ^ 59
def prefixEnd_6429621 : Nat := 4983230072969 + 3 ^ 40 * 6429621 * 2
def baseEnd_6429621 : Nat := 3301485999241893811968217

theorem tailTrace_6429621 : CollatzResearch.WordTrace tailWord_6429621 prefixEnd_6429621 3301485999241893811968217 := by
  unfold tailWord_6429621
  simp only [CollatzResearch.WordTrace]
  refine ⟨234507543439588683688352717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156338362293059122458901811 234507543439588683688352717)
  ·
    refine ⟨87940328789845756383132269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234507543439588683688352717 87940328789845756383132269)
    ·
      refine ⟨32977623296192158643674601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87940328789845756383132269 32977623296192158643674601)
      ·
        refine ⟨24733217472144118982755951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32977623296192158643674601 24733217472144118982755951)
        ·
          refine ⟨37099826208216178474133927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24733217472144118982755951 37099826208216178474133927)
          ·
            refine ⟨55649739312324267711200891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37099826208216178474133927 55649739312324267711200891)
            ·
              refine ⟨83474608968486401566801337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55649739312324267711200891 83474608968486401566801337)
              ·
                refine ⟨62605956726364801175101003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83474608968486401566801337 62605956726364801175101003)
                ·
                  refine ⟨93908935089547201762651505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62605956726364801175101003 93908935089547201762651505)
                  ·
                    refine ⟨70431701317160401321988629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93908935089547201762651505 70431701317160401321988629)
                    ·
                      refine ⟨3301485999241893811968217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70431701317160401321988629 3301485999241893811968217)
                      ·
                        rfl

theorem cell23_6429621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6429621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429621 prefixEnd_6429621 := by exact prefixLift 6429621
  have htrace : WordTrace (prefixWord ++ tailWord_6429621) baseStart_6429621 baseEnd_6429621 := by
    simpa [prefixWord, tailWord_6429621, baseEnd_6429621] using wordTrace_append hprefix tailTrace_6429621
  have hstable : (prefixWord ++ tailWord_6429621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429621).length < 2 ^ (prefixWord ++ tailWord_6429621).sum := by decide
  have hdescent : baseEnd_6429621 < baseStart_6429621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429668 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_6429668 : Nat := 118140960795 + 6429668 * 2 ^ 59
def prefixEnd_6429668 : Nat := 4983230072969 + 3 ^ 40 * 6429668 * 2
def baseEnd_6429668 : Nat := 3301510132832655128080501

theorem tailTrace_6429668 : CollatzResearch.WordTrace tailWord_6429668 prefixEnd_6429668 3301510132832655128080501 := by
  unfold tailWord_6429668
  simp only [CollatzResearch.WordTrace]
  refine ⟨117254628835209205357656829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156339505113612273810209105 117254628835209205357656829)
  ·
    refine ⟨43970485813203452009121311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117254628835209205357656829 43970485813203452009121311)
    ·
      refine ⟨65955728719805178013681967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43970485813203452009121311 65955728719805178013681967)
      ·
        refine ⟨98933593079707767020522951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65955728719805178013681967 98933593079707767020522951)
        ·
          refine ⟨148400389619561650530784427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98933593079707767020522951 148400389619561650530784427)
          ·
            refine ⟨222600584429342475796176641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148400389619561650530784427 222600584429342475796176641)
            ·
              refine ⟨166950438322006856847132481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222600584429342475796176641 166950438322006856847132481)
              ·
                refine ⟨125212828741505142635349361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166950438322006856847132481 125212828741505142635349361)
                ·
                  refine ⟨93909621556128856976512021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125212828741505142635349361 93909621556128856976512021)
                  ·
                    refine ⟨4402013510443540170774001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93909621556128856976512021 4402013510443540170774001)
                    ·
                      refine ⟨3301510132832655128080501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402013510443540170774001 3301510132832655128080501)
                      ·
                        rfl

theorem cell23_6429668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_6429668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429668 prefixEnd_6429668 := by exact prefixLift 6429668
  have htrace : WordTrace (prefixWord ++ tailWord_6429668) baseStart_6429668 baseEnd_6429668 := by
    simpa [prefixWord, tailWord_6429668, baseEnd_6429668] using wordTrace_append hprefix tailTrace_6429668
  have hstable : (prefixWord ++ tailWord_6429668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429668).length < 2 ^ (prefixWord ++ tailWord_6429668).sum := by decide
  have hdescent : baseEnd_6429668 < baseStart_6429668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429669 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 6]
def baseStart_6429669 : Nat := 118140960795 + 6429669 * 2 ^ 59
def prefixEnd_6429669 : Nat := 4983230072969 + 3 ^ 40 * 6429669 * 2
def baseEnd_6429669 : Nat := 366834516257034402685333

theorem tailTrace_6429669 : CollatzResearch.WordTrace tailWord_6429669 prefixEnd_6429669 366834516257034402685333 := by
  unfold tailWord_6429669
  simp only [CollatzResearch.WordTrace]
  refine ⟨234509294143414787886100061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156339529428943191924066707 234509294143414787886100061)
  ·
    refine ⟨87940985303780545457287523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234509294143414787886100061 87940985303780545457287523)
    ·
      refine ⟨131911477955670818185931285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87940985303780545457287523 131911477955670818185931285)
      ·
        refine ⟨6183350529172069602465529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131911477955670818185931285 6183350529172069602465529)
        ·
          refine ⟨4637512896879052201849147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6183350529172069602465529 4637512896879052201849147)
          ·
            refine ⟨6956269345318578302773721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637512896879052201849147 6956269345318578302773721)
            ·
              refine ⟨5217202008988933727080291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6956269345318578302773721 5217202008988933727080291)
              ·
                refine ⟨7825803013483400590620437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217202008988933727080291 7825803013483400590620437)
                ·
                  refine ⟨366834516257034402685333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7825803013483400590620437 366834516257034402685333)
                  ·
                    rfl

theorem cell23_6429669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_6429669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429669 prefixEnd_6429669 := by exact prefixLift 6429669
  have htrace : WordTrace (prefixWord ++ tailWord_6429669) baseStart_6429669 baseEnd_6429669 := by
    simpa [prefixWord, tailWord_6429669, baseEnd_6429669] using wordTrace_append hprefix tailTrace_6429669
  have hstable : (prefixWord ++ tailWord_6429669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429669).length < 2 ^ (prefixWord ++ tailWord_6429669).sum := by decide
  have hdescent : baseEnd_6429669 < baseStart_6429669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429721 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_6429721 : Nat := 118140960795 + 6429721 * 2 ^ 59
def prefixEnd_6429721 : Nat := 4983230072969 + 3 ^ 40 * 6429721 * 2
def baseEnd_6429721 : Nat := 1100512449102447806905919

theorem tailTrace_6429721 : CollatzResearch.WordTrace tailWord_6429721 prefixEnd_6429721 1100512449102447806905919 := by
  unfold tailWord_6429721
  simp only [CollatzResearch.WordTrace]
  refine ⟨234511190739226400766993017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156340793826150933844662011 234511190739226400766993017)
  ·
    refine ⟨175883393054419800575244763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234511190739226400766993017 175883393054419800575244763)
    ·
      refine ⟨263825089581629700862867145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175883393054419800575244763 263825089581629700862867145)
      ·
        refine ⟨197868817186222275647150359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263825089581629700862867145 197868817186222275647150359)
        ·
          refine ⟨296803225779333413470725539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197868817186222275647150359 296803225779333413470725539)
          ·
            refine ⟨445204838669000120206088309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296803225779333413470725539 445204838669000120206088309)
            ·
              refine ⟨41737953625218761269320779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 445204838669000120206088309 41737953625218761269320779)
              ·
                refine ⟨62606930437828141903981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41737953625218761269320779 62606930437828141903981169)
                ·
                  refine ⟨46955197828371106427985877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62606930437828141903981169 46955197828371106427985877)
                  ·
                    refine ⟨1100512449102447806905919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46955197828371106427985877 1100512449102447806905919)
                    ·
                      rfl

theorem cell23_6429721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_6429721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429721 prefixEnd_6429721 := by exact prefixLift 6429721
  have htrace : WordTrace (prefixWord ++ tailWord_6429721) baseStart_6429721 baseEnd_6429721 := by
    simpa [prefixWord, tailWord_6429721, baseEnd_6429721] using wordTrace_append hprefix tailTrace_6429721
  have hstable : (prefixWord ++ tailWord_6429721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429721).length < 2 ^ (prefixWord ++ tailWord_6429721).sum := by decide
  have hdescent : baseEnd_6429721 < baseStart_6429721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429725 : List Nat := [1, 4, 2, 2, 3, 2, 1, 8]
def baseStart_6429725 : Nat := 118140960795 + 6429725 * 2 ^ 59
def prefixEnd_6429725 : Nat := 4983230072969 + 3 ^ 40 * 6429725 * 2
def baseEnd_6429725 : Nat := 122279237082591163150657

theorem tailTrace_6429725 : CollatzResearch.WordTrace tailWord_6429725 prefixEnd_6429725 122279237082591163150657 := by
  unfold tailWord_6429725
  simp only [CollatzResearch.WordTrace]
  refine ⟨234511336631211909450138629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156340891087474606300092419 234511336631211909450138629)
  ·
    refine ⟨43970875618352233021900993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234511336631211909450138629 43970875618352233021900993)
    ·
      refine ⟨32978156713764174766425745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43970875618352233021900993 32978156713764174766425745)
      ·
        refine ⟨24733617535323131074819309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32978156713764174766425745 24733617535323131074819309)
        ·
          refine ⟨9275106575746174153057241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24733617535323131074819309 9275106575746174153057241)
          ·
            refine ⟨6956329931809630614792931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275106575746174153057241 6956329931809630614792931)
            ·
              refine ⟨10434494897714445922189397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956329931809630614792931 10434494897714445922189397)
              ·
                refine ⟨122279237082591163150657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10434494897714445922189397 122279237082591163150657)
                ·
                  rfl

theorem cell23_6429725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 8].length) (baseStart_6429725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429725 prefixEnd_6429725 := by exact prefixLift 6429725
  have htrace : WordTrace (prefixWord ++ tailWord_6429725) baseStart_6429725 baseEnd_6429725 := by
    simpa [prefixWord, tailWord_6429725, baseEnd_6429725] using wordTrace_append hprefix tailTrace_6429725
  have hstable : (prefixWord ++ tailWord_6429725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429725).length < 2 ^ (prefixWord ++ tailWord_6429725).sum := by decide
  have hdescent : baseEnd_6429725 < baseStart_6429725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429745 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_6429745 : Nat := 118140960795 + 6429745 * 2 ^ 59
def prefixEnd_6429745 : Nat := 4983230072969 + 3 ^ 40 * 6429745 * 2
def baseEnd_6429745 : Nat := 3301549670843051326817647

theorem tailTrace_6429745 : CollatzResearch.WordTrace tailWord_6429745 prefixEnd_6429745 3301549670843051326817647 := by
  unfold tailWord_6429745
  simp only [CollatzResearch.WordTrace]
  refine ⟨234512066091139452865866689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156341377394092968577244459 234512066091139452865866689)
  ·
    refine ⟨175884049568354589649400017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234512066091139452865866689 175884049568354589649400017)
    ·
      refine ⟨131913037176265942237050013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175884049568354589649400017 131913037176265942237050013)
      ·
        refine ⟨49467388941099728338893755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131913037176265942237050013 49467388941099728338893755)
        ·
          refine ⟨74201083411649592508340633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49467388941099728338893755 74201083411649592508340633)
          ·
            refine ⟨55650812558737194381255475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74201083411649592508340633 55650812558737194381255475)
            ·
              refine ⟨83476218838105791571883213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55650812558737194381255475 83476218838105791571883213)
              ·
                refine ⟨31303582064289671839456205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83476218838105791571883213 31303582064289671839456205)
                ·
                  refine ⟨11738843274108626939796077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31303582064289671839456205 11738843274108626939796077)
                  ·
                    refine ⟨4402066227790735102423529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11738843274108626939796077 4402066227790735102423529)
                    ·
                      refine ⟨3301549670843051326817647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402066227790735102423529 3301549670843051326817647)
                      ·
                        rfl

theorem cell23_6429745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_6429745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429745 prefixEnd_6429745 := by exact prefixLift 6429745
  have htrace : WordTrace (prefixWord ++ tailWord_6429745) baseStart_6429745 baseEnd_6429745 := by
    simpa [prefixWord, tailWord_6429745, baseEnd_6429745] using wordTrace_append hprefix tailTrace_6429745
  have hstable : (prefixWord ++ tailWord_6429745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429745).length < 2 ^ (prefixWord ++ tailWord_6429745).sum := by decide
  have hdescent : baseEnd_6429745 < baseStart_6429745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429751 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 8]
def baseStart_6429751 : Nat := 118140960795 + 6429751 * 2 ^ 59
def prefixEnd_6429751 : Nat := 4983230072969 + 3 ^ 40 * 6429751 * 2
def baseEnd_6429751 : Nat := 1100517583908992767780873

theorem tailTrace_6429751 : CollatzResearch.WordTrace tailWord_6429751 prefixEnd_6429751 1100517583908992767780873 := by
  unfold tailWord_6429751
  simp only [CollatzResearch.WordTrace]
  refine ⟨234512284929117715890585107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156341523286078477260390071 234512284929117715890585107)
  ·
    refine ⟨351768427393676573835877661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234512284929117715890585107 351768427393676573835877661)
    ·
      refine ⟨131913160272628715188454123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351768427393676573835877661 131913160272628715188454123)
      ·
        refine ⟨197869740408943072782681185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131913160272628715188454123 197869740408943072782681185)
        ·
          refine ⟨148402305306707304587010889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197869740408943072782681185 148402305306707304587010889)
          ·
            refine ⟨111301728980030478440258167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148402305306707304587010889 111301728980030478440258167)
            ·
              refine ⟨166952593470045717660387251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111301728980030478440258167 166952593470045717660387251)
              ·
                refine ⟨250428890205068576490580877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166952593470045717660387251 250428890205068576490580877)
                ·
                  refine ⟨93910833826900716183967829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250428890205068576490580877 93910833826900716183967829)
                  ·
                    refine ⟨1100517583908992767780873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93910833826900716183967829 1100517583908992767780873)
                    ·
                      rfl

theorem cell23_6429751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_6429751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429751 prefixEnd_6429751 := by exact prefixLift 6429751
  have htrace : WordTrace (prefixWord ++ tailWord_6429751) baseStart_6429751 baseEnd_6429751 := by
    simpa [prefixWord, tailWord_6429751, baseEnd_6429751] using wordTrace_append hprefix tailTrace_6429751
  have hstable : (prefixWord ++ tailWord_6429751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429751).length < 2 ^ (prefixWord ++ tailWord_6429751).sum := by decide
  have hdescent : baseEnd_6429751 < baseStart_6429751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429771 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_6429771 : Nat := 118140960795 + 6429771 * 2 ^ 59
def prefixEnd_6429771 : Nat := 4983230072969 + 3 ^ 40 * 6429771 * 2
def baseEnd_6429771 : Nat := 3301563021340068225092527

theorem tailTrace_6429771 : CollatzResearch.WordTrace tailWord_6429771 prefixEnd_6429771 3301563021340068225092527 := by
  unfold tailWord_6429771
  simp only [CollatzResearch.WordTrace]
  refine ⟨234513014389045259306313167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156342009592696839537542111 234513014389045259306313167)
  ·
    refine ⟨351769521583567888959469751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234513014389045259306313167 351769521583567888959469751)
    ·
      refine ⟨527654282375351833439204627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351769521583567888959469751 527654282375351833439204627)
      ·
        refine ⟨791481423563027750158806941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527654282375351833439204627 791481423563027750158806941)
        ·
          refine ⟨296805533836135406309552603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791481423563027750158806941 296805533836135406309552603)
          ·
            refine ⟨445208300754203109464328905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296805533836135406309552603 445208300754203109464328905)
            ·
              refine ⟨333906225565652332098246679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445208300754203109464328905 333906225565652332098246679)
              ·
                refine ⟨500859338348478498147370019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333906225565652332098246679 500859338348478498147370019)
                ·
                  refine ⟨751289007522717747221055029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500859338348478498147370019 751289007522717747221055029)
                  ·
                    refine ⟨70433344455254788801973909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 751289007522717747221055029 70433344455254788801973909)
                    ·
                      refine ⟨3301563021340068225092527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70433344455254788801973909 3301563021340068225092527)
                      ·
                        rfl

theorem cell23_6429771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_6429771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429771 prefixEnd_6429771 := by exact prefixLift 6429771
  have htrace : WordTrace (prefixWord ++ tailWord_6429771) baseStart_6429771 baseEnd_6429771 := by
    simpa [prefixWord, tailWord_6429771, baseEnd_6429771] using wordTrace_append hprefix tailTrace_6429771
  have hstable : (prefixWord ++ tailWord_6429771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429771).length < 2 ^ (prefixWord ++ tailWord_6429771).sum := by decide
  have hdescent : baseEnd_6429771 < baseStart_6429771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
