import V185TrunkScan22Chunk461

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4117451 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 5]
def baseStart_4117451 : Nat := 118140960795 + 4117451 * 2 ^ 59
def prefixEnd_4117451 : Nat := 4983230072969 + 3 ^ 40 * 4117451 * 2
def baseEnd_4117451 : Nat := 469829207630150041717043

theorem tailTrace_4117451 : CollatzResearch.WordTrace tailWord_4117451 prefixEnd_4117451 469829207630150041717043 := by
  unfold tailWord_4117451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150175775406185706490928207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100117183604123804327285471 150175775406185706490928207)
  ·
    refine ⟨225263663109278559736392311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150175775406185706490928207 225263663109278559736392311)
    ·
      refine ⟨337895494663917839604588467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225263663109278559736392311 337895494663917839604588467)
      ·
        refine ⟨506843241995876759406882701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337895494663917839604588467 506843241995876759406882701)
        ·
          refine ⟨190066215748453784777581013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506843241995876759406882701 190066215748453784777581013)
          ·
            refine ⟨4454676931604385580724555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190066215748453784777581013 4454676931604385580724555)
            ·
              refine ⟨6682015397406578371086833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454676931604385580724555 6682015397406578371086833)
              ·
                refine ⟨5011511548054933778315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682015397406578371086833 5011511548054933778315125)
                ·
                  refine ⟨469829207630150041717043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011511548054933778315125 469829207630150041717043)
                  ·
                    rfl

theorem cell22_4117451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].length) (baseStart_4117451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117451 prefixEnd_4117451 := by exact prefixLift 4117451
  have htrace : WordTrace (prefixWord ++ tailWord_4117451) baseStart_4117451 baseEnd_4117451 := by
    simpa [prefixWord, tailWord_4117451, baseEnd_4117451] using wordTrace_append hprefix tailTrace_4117451
  have hstable : (prefixWord ++ tailWord_4117451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117451).length < 2 ^ (prefixWord ++ tailWord_4117451).sum := by decide
  have hdescent : baseEnd_4117451 < baseStart_4117451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117511 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 4, 3]
def baseStart_4117511 : Nat := 118140960795 + 4117511 * 2 ^ 59
def prefixEnd_4117511 : Nat := 4983230072969 + 3 ^ 40 * 4117511 * 2
def baseEnd_4117511 : Nat := 1409508162116629968650945

theorem tailTrace_4117511 : CollatzResearch.WordTrace tailWord_4117511 prefixEnd_4117511 1409508162116629968650945 := by
  unfold tailWord_4117511
  simp only [CollatzResearch.WordTrace]
  refine ⟨150177963785968336738112387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100118642523978891158741591 150177963785968336738112387)
  ·
    refine ⟨225266945678952505107168581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150177963785968336738112387 225266945678952505107168581)
    ·
      refine ⟨42237552314803594707594109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225266945678952505107168581 42237552314803594707594109)
      ·
        refine ⟨15839082118051348015347791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42237552314803594707594109 15839082118051348015347791)
        ·
          refine ⟨23758623177077022023021687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15839082118051348015347791 23758623177077022023021687)
          ·
            refine ⟨35637934765615533034532531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23758623177077022023021687 35637934765615533034532531)
            ·
              refine ⟨53456902148423299551798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35637934765615533034532531 53456902148423299551798797)
              ·
                refine ⟨20046338305658737331924549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53456902148423299551798797 20046338305658737331924549)
                ·
                  refine ⟨3758688432311013249735853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20046338305658737331924549 3758688432311013249735853)
                  ·
                    refine ⟨1409508162116629968650945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758688432311013249735853 1409508162116629968650945)
                    ·
                      rfl

theorem cell22_4117511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_4117511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117511 prefixEnd_4117511 := by exact prefixLift 4117511
  have htrace : WordTrace (prefixWord ++ tailWord_4117511) baseStart_4117511 baseEnd_4117511 := by
    simpa [prefixWord, tailWord_4117511, baseEnd_4117511] using wordTrace_append hprefix tailTrace_4117511
  have hstable : (prefixWord ++ tailWord_4117511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117511).length < 2 ^ (prefixWord ++ tailWord_4117511).sum := by decide
  have hdescent : baseEnd_4117511 < baseStart_4117511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117528 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_4117528 : Nat := 118140960795 + 4117528 * 2 ^ 59
def prefixEnd_4117528 : Nat := 4983230072969 + 3 ^ 40 * 4117528 * 2
def baseEnd_4117528 : Nat := 1409513981564047590975893

theorem tailTrace_4117528 : CollatzResearch.WordTrace tailWord_4117528 prefixEnd_4117528 1409513981564047590975893 := by
  unfold tailWord_4117528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75089291913453374320740619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100119055884604499094320825 75089291913453374320740619)
  ·
    refine ⟨112633937870180061481110929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75089291913453374320740619 112633937870180061481110929)
    ·
      refine ⟨84475453402635046110833197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112633937870180061481110929 84475453402635046110833197)
      ·
        refine ⟨31678295025988142291562449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84475453402635046110833197 31678295025988142291562449)
        ·
          refine ⟨23758721269491106718671837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31678295025988142291562449 23758721269491106718671837)
          ·
            refine ⟨8909520476059165019501939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23758721269491106718671837 8909520476059165019501939)
            ·
              refine ⟨13364280714088747529252909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909520476059165019501939 13364280714088747529252909)
              ·
                refine ⟨5011605267783280323469841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13364280714088747529252909 5011605267783280323469841)
                ·
                  refine ⟨3758703950837460242602381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011605267783280323469841 3758703950837460242602381)
                  ·
                    refine ⟨1409513981564047590975893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758703950837460242602381 1409513981564047590975893)
                    ·
                      rfl

theorem cell22_4117528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_4117528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117528 prefixEnd_4117528 := by exact prefixLift 4117528
  have htrace : WordTrace (prefixWord ++ tailWord_4117528) baseStart_4117528 baseEnd_4117528 := by
    simpa [prefixWord, tailWord_4117528, baseEnd_4117528] using wordTrace_append hprefix tailTrace_4117528
  have hstable : (prefixWord ++ tailWord_4117528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117528).length < 2 ^ (prefixWord ++ tailWord_4117528).sum := by decide
  have hdescent : baseEnd_4117528 < baseStart_4117528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117543 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4117543 : Nat := 118140960795 + 4117543 * 2 ^ 59
def prefixEnd_4117543 : Nat := 4983230072969 + 3 ^ 40 * 4117543 * 2
def baseEnd_4117543 : Nat := 1409519116370592551850847

theorem tailTrace_4117543 : CollatzResearch.WordTrace tailWord_4117543 prefixEnd_4117543 1409519116370592551850847 := by
  unfold tailWord_4117543
  simp only [CollatzResearch.WordTrace]
  refine ⟨150179130921852406203277283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100119420614568270802184855 150179130921852406203277283)
  ·
    refine ⟨225268696382778609304915925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150179130921852406203277283 225268696382778609304915925)
    ·
      refine ⟨5279735071471373655583967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225268696382778609304915925 5279735071471373655583967)
      ·
        refine ⟨7919602607207060483375951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279735071471373655583967 7919602607207060483375951)
        ·
          refine ⟨11879403910810590725063927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919602607207060483375951 11879403910810590725063927)
          ·
            refine ⟨17819105866215886087595891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879403910810590725063927 17819105866215886087595891)
            ·
              refine ⟨26728658799323829131393837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819105866215886087595891 26728658799323829131393837)
              ·
                refine ⟨10023247049746435924272689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26728658799323829131393837 10023247049746435924272689)
                ·
                  refine ⟨7517435287309826943204517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10023247049746435924272689 7517435287309826943204517)
                  ·
                    refine ⟨1409519116370592551850847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517435287309826943204517 1409519116370592551850847)
                    ·
                      rfl

theorem cell22_4117543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4117543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117543 prefixEnd_4117543 := by exact prefixLift 4117543
  have htrace : WordTrace (prefixWord ++ tailWord_4117543) baseStart_4117543 baseEnd_4117543 := by
    simpa [prefixWord, tailWord_4117543, baseEnd_4117543] using wordTrace_append hprefix tailTrace_4117543
  have hstable : (prefixWord ++ tailWord_4117543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117543).length < 2 ^ (prefixWord ++ tailWord_4117543).sum := by decide
  have hdescent : baseEnd_4117543 < baseStart_4117543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117650 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4117650 : Nat := 118140960795 + 4117650 * 2 ^ 59
def prefixEnd_4117650 : Nat := 4983230072969 + 3 ^ 40 * 4117650 * 2
def baseEnd_4117650 : Nat := 1409555744657279939425519

theorem tailTrace_4117650 : CollatzResearch.WordTrace tailWord_4117650 prefixEnd_4117650 1409555744657279939425519 := by
  unfold tailWord_4117650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37545758383116190869355601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100122022354976508984948269 37545758383116190869355601)
  ·
    refine ⟨28159318787337143152016701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37545758383116190869355601 28159318787337143152016701)
    ·
      refine ⟨10559744545251428682006263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28159318787337143152016701 10559744545251428682006263)
      ·
        refine ⟨15839616817877143023009395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10559744545251428682006263 15839616817877143023009395)
        ·
          refine ⟨23759425226815714534514093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15839616817877143023009395 23759425226815714534514093)
          ·
            refine ⟨8909784460055892950442785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23759425226815714534514093 8909784460055892950442785)
            ·
              refine ⟨6682338345041919712832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909784460055892950442785 6682338345041919712832089)
              ·
                refine ⟨5011753758781439784624067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682338345041919712832089 5011753758781439784624067)
                ·
                  refine ⟨7517630638172159676936101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011753758781439784624067 7517630638172159676936101)
                  ·
                    refine ⟨1409555744657279939425519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517630638172159676936101 1409555744657279939425519)
                    ·
                      rfl

theorem cell22_4117650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4117650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117650 prefixEnd_4117650 := by exact prefixLift 4117650
  have htrace : WordTrace (prefixWord ++ tailWord_4117650) baseStart_4117650 baseEnd_4117650 := by
    simpa [prefixWord, tailWord_4117650, baseEnd_4117650] using wordTrace_append hprefix tailTrace_4117650
  have hstable : (prefixWord ++ tailWord_4117650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117650).length < 2 ^ (prefixWord ++ tailWord_4117650).sum := by decide
  have hdescent : baseEnd_4117650 < baseStart_4117650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117661 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4117661 : Nat := 118140960795 + 4117661 * 2 ^ 59
def prefixEnd_4117661 : Nat := 4983230072969 + 3 ^ 40 * 4117661 * 2
def baseEnd_4117661 : Nat := 1409559510182079577400485

theorem tailTrace_4117661 : CollatzResearch.WordTrace tailWord_4117661 prefixEnd_4117661 1409559510182079577400485 := by
  unfold tailWord_4117661
  simp only [CollatzResearch.WordTrace]
  refine ⟨150183434735424912356072837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100122289823616608237381891 150183434735424912356072837)
  ·
    refine ⟨28159394012892171066763657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150183434735424912356072837 28159394012892171066763657)
    ·
      refine ⟨21119545509669128300072743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28159394012892171066763657 21119545509669128300072743)
      ·
        refine ⟨31679318264503692450109115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21119545509669128300072743 31679318264503692450109115)
        ·
          refine ⟨47518977396755538675163673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679318264503692450109115 47518977396755538675163673)
          ·
            refine ⟨35639233047566654006372755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47518977396755538675163673 35639233047566654006372755)
            ·
              refine ⟨53458849571349981009559133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35639233047566654006372755 53458849571349981009559133)
              ·
                refine ⟨20047068589256242878584675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53458849571349981009559133 20047068589256242878584675)
                ·
                  refine ⟨30070602883884364317877013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20047068589256242878584675 30070602883884364317877013)
                  ·
                    refine ⟨1409559510182079577400485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30070602883884364317877013 1409559510182079577400485)
                    ·
                      rfl

theorem cell22_4117661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4117661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117661 prefixEnd_4117661 := by exact prefixLift 4117661
  have htrace : WordTrace (prefixWord ++ tailWord_4117661) baseStart_4117661 baseEnd_4117661 := by
    simpa [prefixWord, tailWord_4117661, baseEnd_4117661] using wordTrace_append hprefix tailTrace_4117661
  have hstable : (prefixWord ++ tailWord_4117661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117661).length < 2 ^ (prefixWord ++ tailWord_4117661).sum := by decide
  have hdescent : baseEnd_4117661 < baseStart_4117661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117697 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4117697 : Nat := 118140960795 + 4117697 * 2 ^ 59
def prefixEnd_4117697 : Nat := 4983230072969 + 3 ^ 40 * 4117697 * 2
def baseEnd_4117697 : Nat := 1409571833717787483500375

theorem tailTrace_4117697 : CollatzResearch.WordTrace tailWord_4117697 prefixEnd_4117697 1409571833717787483500375 := by
  unfold tailWord_4117697
  simp only [CollatzResearch.WordTrace]
  refine ⟨150184747763294490504383345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100123165175529660336255563 150184747763294490504383345)
  ·
    refine ⟨112638560822470867878287509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150184747763294490504383345 112638560822470867878287509)
    ·
      refine ⟨5279932538553321931794727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112638560822470867878287509 5279932538553321931794727)
      ·
        refine ⟨7919898807829982897692091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279932538553321931794727 7919898807829982897692091)
        ·
          refine ⟨11879848211744974346538137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919898807829982897692091 11879848211744974346538137)
          ·
            refine ⟨8909886158808730759903603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11879848211744974346538137 8909886158808730759903603)
            ·
              refine ⟨13364829238213096139855405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909886158808730759903603 13364829238213096139855405)
              ·
                refine ⟨5011810964329911052445777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13364829238213096139855405 5011810964329911052445777)
                ·
                  refine ⟨3758858223247433289334333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011810964329911052445777 3758858223247433289334333)
                  ·
                    refine ⟨1409571833717787483500375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758858223247433289334333 1409571833717787483500375)
                    ·
                      rfl

theorem cell22_4117697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4117697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117697 prefixEnd_4117697 := by exact prefixLift 4117697
  have htrace : WordTrace (prefixWord ++ tailWord_4117697) baseStart_4117697 baseEnd_4117697 := by
    simpa [prefixWord, tailWord_4117697, baseEnd_4117697] using wordTrace_append hprefix tailTrace_4117697
  have hstable : (prefixWord ++ tailWord_4117697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117697).length < 2 ^ (prefixWord ++ tailWord_4117697).sum := by decide
  have hdescent : baseEnd_4117697 < baseStart_4117697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117738 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_4117738 : Nat := 118140960795 + 4117738 * 2 ^ 59
def prefixEnd_4117738 : Nat := 4983230072969 + 3 ^ 40 * 4117738 * 2
def baseEnd_4117738 : Nat := 469861956285225681075083

theorem tailTrace_4117738 : CollatzResearch.WordTrace tailWord_4117738 prefixEnd_4117738 469861956285225681075083 := by
  unfold tailWord_4117738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37546560789036488626656467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100124162104097303004417245 37546560789036488626656467)
  ·
    refine ⟨56319841183554732939984701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37546560789036488626656467 56319841183554732939984701)
    ·
      refine ⟨21119940443833024852494263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56319841183554732939984701 21119940443833024852494263)
      ·
        refine ⟨31679910665749537278741395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21119940443833024852494263 31679910665749537278741395)
        ·
          refine ⟨47519865998624305918112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679910665749537278741395 47519865998624305918112093)
          ·
            refine ⟨17819949749484114719292035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47519865998624305918112093 17819949749484114719292035)
            ·
              refine ⟨26729924624226172078938053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819949749484114719292035 26729924624226172078938053)
              ·
                refine ⟨5011860867042407264800885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26729924624226172078938053 5011860867042407264800885)
                ·
                  refine ⟨469861956285225681075083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011860867042407264800885 469861956285225681075083)
                  ·
                    rfl

theorem cell22_4117738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_4117738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117738 prefixEnd_4117738 := by exact prefixLift 4117738
  have htrace : WordTrace (prefixWord ++ tailWord_4117738) baseStart_4117738 baseEnd_4117738 := by
    simpa [prefixWord, tailWord_4117738, baseEnd_4117738] using wordTrace_append hprefix tailTrace_4117738
  have hstable : (prefixWord ++ tailWord_4117738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117738).length < 2 ^ (prefixWord ++ tailWord_4117738).sum := by decide
  have hdescent : baseEnd_4117738 < baseStart_4117738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117800 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_4117800 : Nat := 118140960795 + 4117800 * 2 ^ 59
def prefixEnd_4117800 : Nat := 4983230072969 + 3 ^ 40 * 4117800 * 2
def baseEnd_4117800 : Nat := 469869030907576516058353

theorem tailTrace_4117800 : CollatzResearch.WordTrace tailWord_4117800 prefixEnd_4117800 469869030907576516058353 := by
  unfold tailWord_4117800
  simp only [CollatzResearch.WordTrace]
  refine ⟨75094252240960669547691427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100125669654614226063588569 75094252240960669547691427)
  ·
    refine ⟨112641378361441004321537141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75094252240960669547691427 112641378361441004321537141)
    ·
      refine ⟨10560129221385094155144107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112641378361441004321537141 10560129221385094155144107)
      ·
        refine ⟨15840193832077641232716161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560129221385094155144107 15840193832077641232716161)
        ·
          refine ⟨11880145374058230924537121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15840193832077641232716161 11880145374058230924537121)
          ·
            refine ⟨8910109030543673193402841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11880145374058230924537121 8910109030543673193402841)
            ·
              refine ⟨6682581772907754895052131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910109030543673193402841 6682581772907754895052131)
              ·
                refine ⟨10023872659361632342578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682581772907754895052131 10023872659361632342578197)
                ·
                  refine ⟨469869030907576516058353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10023872659361632342578197 469869030907576516058353)
                  ·
                    rfl

theorem cell22_4117800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_4117800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117800 prefixEnd_4117800 := by exact prefixLift 4117800
  have htrace : WordTrace (prefixWord ++ tailWord_4117800) baseStart_4117800 baseEnd_4117800 := by
    simpa [prefixWord, tailWord_4117800, baseEnd_4117800] using wordTrace_append hprefix tailTrace_4117800
  have hstable : (prefixWord ++ tailWord_4117800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117800).length < 2 ^ (prefixWord ++ tailWord_4117800).sum := by decide
  have hdescent : baseEnd_4117800 < baseStart_4117800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117813 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4117813 : Nat := 118140960795 + 4117813 * 2 ^ 59
def prefixEnd_4117813 : Nat := 4983230072969 + 3 ^ 40 * 4117813 * 2
def baseEnd_4117813 : Nat := 1409611542888401847600019

theorem tailTrace_4117813 : CollatzResearch.WordTrace tailWord_4117813 prefixEnd_4117813 1409611542888401847600019 := by
  unfold tailWord_4117813
  simp only [CollatzResearch.WordTrace]
  refine ⟨150188978630874242315606093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100125985753916161543737395 150188978630874242315606093)
  ·
    refine ⟨56320866986577840868352285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150188978630874242315606093 56320866986577840868352285)
    ·
      refine ⟨21120325119966690325632107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56320866986577840868352285 21120325119966690325632107)
      ·
        refine ⟨31680487679950035488448161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21120325119966690325632107 31680487679950035488448161)
        ·
          refine ⟨23760365759962526616336121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31680487679950035488448161 23760365759962526616336121)
          ·
            refine ⟨17820274319971894962252091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23760365759962526616336121 17820274319971894962252091)
            ·
              refine ⟨26730411479957842443378137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17820274319971894962252091 26730411479957842443378137)
              ·
                refine ⟨20047808609968381832533603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26730411479957842443378137 20047808609968381832533603)
                ·
                  refine ⟨30071712914952572748800405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20047808609968381832533603 30071712914952572748800405)
                  ·
                    refine ⟨1409611542888401847600019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30071712914952572748800405 1409611542888401847600019)
                    ·
                      rfl

theorem cell22_4117813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4117813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117813 prefixEnd_4117813 := by exact prefixLift 4117813
  have htrace : WordTrace (prefixWord ++ tailWord_4117813) baseStart_4117813 baseEnd_4117813 := by
    simpa [prefixWord, tailWord_4117813, baseEnd_4117813] using wordTrace_append hprefix tailTrace_4117813
  have hstable : (prefixWord ++ tailWord_4117813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117813).length < 2 ^ (prefixWord ++ tailWord_4117813).sum := by decide
  have hdescent : baseEnd_4117813 < baseStart_4117813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117866 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_4117866 : Nat := 118140960795 + 4117866 * 2 ^ 59
def prefixEnd_4117866 : Nat := 4983230072969 + 3 ^ 40 * 4117866 * 2
def baseEnd_4117866 : Nat := 1409629685871527376024857

theorem tailTrace_4117866 : CollatzResearch.WordTrace tailWord_4117866 prefixEnd_4117866 1409629685871527376024857 := by
  unfold tailWord_4117866
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547727924920558091821363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100127274466454821578190301 37547727924920558091821363)
  ·
    refine ⟨56321591887380837137732045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37547727924920558091821363 56321591887380837137732045)
    ·
      refine ⟨21120596957767813926649517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56321591887380837137732045 21120596957767813926649517)
      ·
        refine ⟨7920223859162930222493569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21120596957767813926649517 7920223859162930222493569)
        ·
          refine ⟨5940167894372197666870177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920223859162930222493569 5940167894372197666870177)
          ·
            refine ⟨4455125920779148250152633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940167894372197666870177 4455125920779148250152633)
            ·
              refine ⟨3341344440584361187614475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455125920779148250152633 3341344440584361187614475)
              ·
                refine ⟨5012016660876541781421713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341344440584361187614475 5012016660876541781421713)
                ·
                  refine ⟨3759012495657406336066285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012016660876541781421713 3759012495657406336066285)
                  ·
                    refine ⟨1409629685871527376024857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759012495657406336066285 1409629685871527376024857)
                    ·
                      rfl

theorem cell22_4117866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_4117866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117866 prefixEnd_4117866 := by exact prefixLift 4117866
  have htrace : WordTrace (prefixWord ++ tailWord_4117866) baseStart_4117866 baseEnd_4117866 := by
    simpa [prefixWord, tailWord_4117866, baseEnd_4117866] using wordTrace_append hprefix tailTrace_4117866
  have hstable : (prefixWord ++ tailWord_4117866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117866).length < 2 ^ (prefixWord ++ tailWord_4117866).sum := by decide
  have hdescent : baseEnd_4117866 < baseStart_4117866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117967 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 2, 3]
def baseStart_4117967 : Nat := 118140960795 + 4117967 * 2 ^ 59
def prefixEnd_4117967 : Nat := 4983230072969 + 3 ^ 40 * 4117967 * 2
def baseEnd_4117967 : Nat := 1409664260235596779249547

theorem tailTrace_4117967 : CollatzResearch.WordTrace tailWord_4117967 prefixEnd_4117967 1409664260235596779249547 := by
  unfold tailWord_4117967
  simp only [CollatzResearch.WordTrace]
  refine ⟨150194595472316326616712155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100129730314877551077808103 150194595472316326616712155)
  ·
    refine ⟨225291893208474489925068233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150194595472316326616712155 225291893208474489925068233)
    ·
      refine ⟨168968919906355867443801175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225291893208474489925068233 168968919906355867443801175)
      ·
        refine ⟨253453379859533801165701763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168968919906355867443801175 253453379859533801165701763)
        ·
          refine ⟨380180069789300701748552645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253453379859533801165701763 380180069789300701748552645)
          ·
            refine ⟨71283763085493881577853621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380180069789300701748552645 71283763085493881577853621)
            ·
              refine ⟨6682852789265051397923777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71283763085493881577853621 6682852789265051397923777)
              ·
                refine ⟨5012139591948788548442833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682852789265051397923777 5012139591948788548442833)
                ·
                  refine ⟨3759104693961591411332125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012139591948788548442833 3759104693961591411332125)
                  ·
                    refine ⟨1409664260235596779249547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759104693961591411332125 1409664260235596779249547)
                    ·
                      rfl

theorem cell22_4117967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_4117967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117967 prefixEnd_4117967 := by exact prefixLift 4117967
  have htrace : WordTrace (prefixWord ++ tailWord_4117967) baseStart_4117967 baseEnd_4117967 := by
    simpa [prefixWord, tailWord_4117967, baseEnd_4117967] using wordTrace_append hprefix tailTrace_4117967
  have hstable : (prefixWord ++ tailWord_4117967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117967).length < 2 ^ (prefixWord ++ tailWord_4117967).sum := by decide
  have hdescent : baseEnd_4117967 < baseStart_4117967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117993 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_4117993 : Nat := 118140960795 + 4117993 * 2 ^ 59
def prefixEnd_4117993 : Nat := 4983230072969 + 3 ^ 40 * 4117993 * 2
def baseEnd_4117993 : Nat := 1409673160566941378099467

theorem tailTrace_4117993 : CollatzResearch.WordTrace tailWord_4117993 prefixEnd_4117993 1409673160566941378099467 := by
  unfold tailWord_4117993
  simp only [CollatzResearch.WordTrace]
  refine ⟨150195543770222133057158633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100130362513481422038105755 150195543770222133057158633)
  ·
    refine ⟨112646657827666599792868975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150195543770222133057158633 112646657827666599792868975)
    ·
      refine ⟨168969986741499899689303463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112646657827666599792868975 168969986741499899689303463)
      ·
        refine ⟨253454980112249849533955195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168969986741499899689303463 253454980112249849533955195)
        ·
          refine ⟨380182470168374774300932793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253454980112249849533955195 380182470168374774300932793)
          ·
            refine ⟨285136852626281080725699595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380182470168374774300932793 285136852626281080725699595)
            ·
              refine ⟨427705278939421621088549393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285136852626281080725699595 427705278939421621088549393)
              ·
                refine ⟨320778959204566215816412045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427705278939421621088549393 320778959204566215816412045)
                ·
                  refine ⟨120292109701712330931154517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320778959204566215816412045 120292109701712330931154517)
                  ·
                    refine ⟨1409673160566941378099467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120292109701712330931154517 1409673160566941378099467)
                    ·
                      rfl

theorem cell22_4117993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_4117993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117993 prefixEnd_4117993 := by exact prefixLift 4117993
  have htrace : WordTrace (prefixWord ++ tailWord_4117993) baseStart_4117993 baseEnd_4117993 := by
    simpa [prefixWord, tailWord_4117993, baseEnd_4117993] using wordTrace_append hprefix tailTrace_4117993
  have hstable : (prefixWord ++ tailWord_4117993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117993).length < 2 ^ (prefixWord ++ tailWord_4117993).sum := by decide
  have hdescent : baseEnd_4117993 < baseStart_4117993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117995 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 5, 3]
def baseStart_4117995 : Nat := 118140960795 + 4117995 * 2 ^ 59
def prefixEnd_4117995 : Nat := 4983230072969 + 3 ^ 40 * 4117995 * 2
def baseEnd_4117995 : Nat := 1409673845207814039549461

theorem tailTrace_4117995 : CollatzResearch.WordTrace tailWord_4117995 prefixEnd_4117995 1409673845207814039549461 := by
  unfold tailWord_4117995
  simp only [CollatzResearch.WordTrace]
  refine ⟨150195616716214887398731439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100130411144143258265820959 150195616716214887398731439)
  ·
    refine ⟨225293425074322331098097159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150195616716214887398731439 225293425074322331098097159)
    ·
      refine ⟨337940137611483496647145739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225293425074322331098097159 337940137611483496647145739)
      ·
        refine ⟨506910206417225244970718609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337940137611483496647145739 506910206417225244970718609)
        ·
          refine ⟨380182654812918933728038957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506910206417225244970718609 380182654812918933728038957)
          ·
            refine ⟨142568495554844600148014609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380182654812918933728038957 142568495554844600148014609)
            ·
              refine ⟨106926371666133450111010957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142568495554844600148014609 106926371666133450111010957)
              ·
                refine ⟨40097389374800043791629109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106926371666133450111010957 40097389374800043791629109)
                ·
                  refine ⟨3759130253887504105465229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40097389374800043791629109 3759130253887504105465229)
                  ·
                    refine ⟨1409673845207814039549461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759130253887504105465229 1409673845207814039549461)
                    ·
                      rfl

theorem cell22_4117995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].length) (baseStart_4117995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117995 prefixEnd_4117995 := by exact prefixLift 4117995
  have htrace : WordTrace (prefixWord ++ tailWord_4117995) baseStart_4117995 baseEnd_4117995 := by
    simpa [prefixWord, tailWord_4117995, baseEnd_4117995] using wordTrace_append hprefix tailTrace_4117995
  have hstable : (prefixWord ++ tailWord_4117995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117995).length < 2 ^ (prefixWord ++ tailWord_4117995).sum := by decide
  have hdescent : baseEnd_4117995 < baseStart_4117995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117997 : List Nat := [1, 5, 1, 3, 2, 1, 1, 8]
def baseStart_4117997 : Nat := 118140960795 + 4117997 * 2 ^ 59
def prefixEnd_4117997 : Nat := 4983230072969 + 3 ^ 40 * 4117997 * 2
def baseEnd_4117997 : Nat := 156630503316520744555495

theorem tailTrace_4117997 : CollatzResearch.WordTrace tailWord_4117997 prefixEnd_4117997 156630503316520744555495 := by
  unfold tailWord_4117997
  simp only [CollatzResearch.WordTrace]
  refine ⟨150195689662207641740304245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100130459774805094493536163 150195689662207641740304245)
  ·
    refine ⟨14080845905831966413153523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150195689662207641740304245 14080845905831966413153523)
    ·
      refine ⟨21121268858747949619730285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14080845905831966413153523 21121268858747949619730285)
      ·
        refine ⟨7920475822030481107398857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21121268858747949619730285 7920475822030481107398857)
        ·
          refine ⟨5940356866522860830549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920475822030481107398857 5940356866522860830549143)
          ·
            refine ⟨8910535299784291245823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940356866522860830549143 8910535299784291245823715)
            ·
              refine ⟨13365802949676436868735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8910535299784291245823715 13365802949676436868735573)
              ·
                refine ⟨156630503316520744555495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13365802949676436868735573 156630503316520744555495)
                ·
                  rfl

theorem cell22_4117997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 8].length) (baseStart_4117997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4117997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4117997 prefixEnd_4117997 := by exact prefixLift 4117997
  have htrace : WordTrace (prefixWord ++ tailWord_4117997) baseStart_4117997 baseEnd_4117997 := by
    simpa [prefixWord, tailWord_4117997, baseEnd_4117997] using wordTrace_append hprefix tailTrace_4117997
  have hstable : (prefixWord ++ tailWord_4117997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117997).length < 2 ^ (prefixWord ++ tailWord_4117997).sum := by decide
  have hdescent : baseEnd_4117997 < baseStart_4117997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118014 : List Nat := [4, 2, 2, 3, 1, 2, 8]
def baseStart_4118014 : Nat := 118140960795 + 4118014 * 2 ^ 59
def prefixEnd_4118014 : Nat := 4983230072969 + 3 ^ 40 * 4118014 * 2
def baseEnd_4118014 : Nat := 52210383307263123086089

theorem tailTrace_4118014 : CollatzResearch.WordTrace tailWord_4118014 prefixEnd_4118014 52210383307263123086089 := by
  unfold tailWord_4118014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774538712893256705459137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100130873135430702429115397 18774538712893256705459137)
  ·
    refine ⟨14080904034669942529094353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18774538712893256705459137 14080904034669942529094353)
    ·
      refine ⟨10560678026002456896820765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14080904034669942529094353 10560678026002456896820765)
      ·
        refine ⟨3960254259750921336307787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10560678026002456896820765 3960254259750921336307787)
        ·
          refine ⟨5940381389626382004461681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960254259750921336307787 5940381389626382004461681)
          ·
            refine ⟨4455286042219786503346261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940381389626382004461681 4455286042219786503346261)
            ·
              refine ⟨52210383307263123086089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4455286042219786503346261 52210383307263123086089)
              ·
                rfl

theorem cell22_4118014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 8].length) (baseStart_4118014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118014 prefixEnd_4118014 := by exact prefixLift 4118014
  have htrace : WordTrace (prefixWord ++ tailWord_4118014) baseStart_4118014 baseEnd_4118014 := by
    simpa [prefixWord, tailWord_4118014, baseEnd_4118014] using wordTrace_append hprefix tailTrace_4118014
  have hstable : (prefixWord ++ tailWord_4118014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118014).length < 2 ^ (prefixWord ++ tailWord_4118014).sum := by decide
  have hdescent : baseEnd_4118014 < baseStart_4118014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118025 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 5]
def baseStart_4118025 : Nat := 118140960795 + 4118025 * 2 ^ 59
def prefixEnd_4118025 : Nat := 4983230072969 + 3 ^ 40 * 4118025 * 2
def baseEnd_4118025 : Nat := 469894704940301320433123

theorem tailTrace_4118025 : CollatzResearch.WordTrace tailWord_4118025 prefixEnd_4118025 469894704940301320433123 := by
  unfold tailWord_4118025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150196710906106202522323529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100131140604070801681549019 150196710906106202522323529)
  ·
    refine ⟨112647533179579651891742647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150196710906106202522323529 112647533179579651891742647)
    ·
      refine ⟨168971299769369477837613971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112647533179579651891742647 168971299769369477837613971)
      ·
        refine ⟨253456949654054216756420957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168971299769369477837613971 253456949654054216756420957)
        ·
          refine ⟨95046356120270331283657859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253456949654054216756420957 95046356120270331283657859)
          ·
            refine ⟨142569534180405496925486789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95046356120270331283657859 142569534180405496925486789)
            ·
              refine ⟨26731787658826030673528773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142569534180405496925486789 26731787658826030673528773)
              ·
                refine ⟨5012210186029880751286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26731787658826030673528773 5012210186029880751286645)
                ·
                  refine ⟨469894704940301320433123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5012210186029880751286645 469894704940301320433123)
                  ·
                    rfl

theorem cell22_4118025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_4118025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118025 prefixEnd_4118025 := by exact prefixLift 4118025
  have htrace : WordTrace (prefixWord ++ tailWord_4118025) baseStart_4118025 baseEnd_4118025 := by
    simpa [prefixWord, tailWord_4118025, baseEnd_4118025] using wordTrace_append hprefix tailTrace_4118025
  have hstable : (prefixWord ++ tailWord_4118025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118025).length < 2 ^ (prefixWord ++ tailWord_4118025).sum := by decide
  have hdescent : baseEnd_4118025 < baseStart_4118025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118085 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_4118085 : Nat := 118140960795 + 4118085 * 2 ^ 59
def prefixEnd_4118085 : Nat := 4983230072969 + 3 ^ 40 * 4118085 * 2
def baseEnd_4118085 : Nat := 1409704654047083804799185

theorem tailTrace_4118085 : CollatzResearch.WordTrace tailWord_4118085 prefixEnd_4118085 1409704654047083804799185 := by
  unfold tailWord_4118085
  simp only [CollatzResearch.WordTrace]
  refine ⟨150198899285888832769507709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100132599523925888513005139 150198899285888832769507709)
  ·
    refine ⟨56324587232208312288565391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150198899285888832769507709 56324587232208312288565391)
    ·
      refine ⟨84486880848312468432848087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56324587232208312288565391 84486880848312468432848087)
      ·
        refine ⟨126730321272468702649272131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84486880848312468432848087 126730321272468702649272131)
        ·
          refine ⟨190095481908703053973908197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126730321272468702649272131 190095481908703053973908197)
          ·
            refine ⟨35642902857881822620107787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190095481908703053973908197 35642902857881822620107787)
            ·
              refine ⟨53464354286822733930161681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35642902857881822620107787 53464354286822733930161681)
              ·
                refine ⟨40098265715117050447621261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53464354286822733930161681 40098265715117050447621261)
                ·
                  refine ⟨15036849643168893917857973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40098265715117050447621261 15036849643168893917857973)
                  ·
                    refine ⟨1409704654047083804799185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15036849643168893917857973 1409704654047083804799185)
                    ·
                      rfl

theorem cell22_4118085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_4118085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118085 prefixEnd_4118085 := by exact prefixLift 4118085
  have htrace : WordTrace (prefixWord ++ tailWord_4118085) baseStart_4118085 baseEnd_4118085 := by
    simpa [prefixWord, tailWord_4118085, baseEnd_4118085] using wordTrace_append hprefix tailTrace_4118085
  have hstable : (prefixWord ++ tailWord_4118085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118085).length < 2 ^ (prefixWord ++ tailWord_4118085).sum := by decide
  have hdescent : baseEnd_4118085 < baseStart_4118085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118117 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_4118117 : Nat := 118140960795 + 4118117 * 2 ^ 59
def prefixEnd_4118117 : Nat := 4983230072969 + 3 ^ 40 * 4118117 * 2
def baseEnd_4118117 : Nat := 1409715608301046387999087

theorem tailTrace_4118117 : CollatzResearch.WordTrace tailWord_4118117 prefixEnd_4118117 1409715608301046387999087 := by
  unfold tailWord_4118117
  simp only [CollatzResearch.WordTrace]
  refine ⟨150200066421772902234672605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100133377614515268156448403 150200066421772902234672605)
  ·
    refine ⟨56325024908164838338002227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150200066421772902234672605 56325024908164838338002227)
    ·
      refine ⟨84487537362247257507003341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56325024908164838338002227 84487537362247257507003341)
      ·
        refine ⟨31682826510842721565126253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84487537362247257507003341 31682826510842721565126253)
        ·
          refine ⟨11881059941566020586922345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31682826510842721565126253 11881059941566020586922345)
          ·
            refine ⟨8910794956174515440191759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11881059941566020586922345 8910794956174515440191759)
            ·
              refine ⟨13366192434261773160287639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8910794956174515440191759 13366192434261773160287639)
              ·
                refine ⟨20049288651392659740431459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366192434261773160287639 20049288651392659740431459)
                ·
                  refine ⟨30073932977088989610647189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20049288651392659740431459 30073932977088989610647189)
                  ·
                    refine ⟨1409715608301046387999087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30073932977088989610647189 1409715608301046387999087)
                    ·
                      rfl

theorem cell22_4118117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_4118117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118117 prefixEnd_4118117 := by exact prefixLift 4118117
  have htrace : WordTrace (prefixWord ++ tailWord_4118117) baseStart_4118117 baseEnd_4118117 := by
    simpa [prefixWord, tailWord_4118117, baseEnd_4118117] using wordTrace_append hprefix tailTrace_4118117
  have hstable : (prefixWord ++ tailWord_4118117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118117).length < 2 ^ (prefixWord ++ tailWord_4118117).sum := by decide
  have hdescent : baseEnd_4118117 < baseStart_4118117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118177 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 7]
def baseStart_4118177 : Nat := 118140960795 + 4118177 * 2 ^ 59
def prefixEnd_4118177 : Nat := 4983230072969 + 3 ^ 40 * 4118177 * 2
def baseEnd_4118177 : Nat := 469912049175742077166301

theorem tailTrace_4118177 : CollatzResearch.WordTrace tailWord_4118177 prefixEnd_4118177 469912049175742077166301 := by
  unfold tailWord_4118177
  simp only [CollatzResearch.WordTrace]
  refine ⟨150202254801555532481856785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100134836534370354987904523 150202254801555532481856785)
  ·
    refine ⟨112651691101166649361392589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150202254801555532481856785 112651691101166649361392589)
    ·
      refine ⟨42244384162937493510522221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112651691101166649361392589 42244384162937493510522221)
      ·
        refine ⟨15841644061101560066445833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42244384162937493510522221 15841644061101560066445833)
        ·
          refine ⟨11881233045826170049834375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15841644061101560066445833 11881233045826170049834375)
          ·
            refine ⟨17821849568739255074751563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881233045826170049834375 17821849568739255074751563)
            ·
              refine ⟨26732774353108882612127345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17821849568739255074751563 26732774353108882612127345)
              ·
                refine ⟨20049580764831661959095509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26732774353108882612127345 20049580764831661959095509)
                ·
                  refine ⟨469912049175742077166301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20049580764831661959095509 469912049175742077166301)
                  ·
                    rfl

theorem cell22_4118177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_4118177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118177 prefixEnd_4118177 := by exact prefixLift 4118177
  have htrace : WordTrace (prefixWord ++ tailWord_4118177) baseStart_4118177 baseEnd_4118177 := by
    simpa [prefixWord, tailWord_4118177, baseEnd_4118177] using wordTrace_append hprefix tailTrace_4118177
  have hstable : (prefixWord ++ tailWord_4118177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118177).length < 2 ^ (prefixWord ++ tailWord_4118177).sum := by decide
  have hdescent : baseEnd_4118177 < baseStart_4118177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118181 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_4118181 : Nat := 118140960795 + 4118181 * 2 ^ 59
def prefixEnd_4118181 : Nat := 4983230072969 + 3 ^ 40 * 4118181 * 2
def baseEnd_4118181 : Nat := 1409737516808971554398891

theorem tailTrace_4118181 : CollatzResearch.WordTrace tailWord_4118181 prefixEnd_4118181 1409737516808971554398891 := by
  unfold tailWord_4118181
  simp only [CollatzResearch.WordTrace]
  refine ⟨150202400693541041165002397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100134933795694027443334931 150202400693541041165002397)
  ·
    refine ⟨56325900260077890436875899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150202400693541041165002397 56325900260077890436875899)
    ·
      refine ⟨84488850390116835655313849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56325900260077890436875899 84488850390116835655313849)
      ·
        refine ⟨63366637792587626741485387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84488850390116835655313849 63366637792587626741485387)
        ·
          refine ⟨95049956688881440112228081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63366637792587626741485387 95049956688881440112228081)
          ·
            refine ⟨71287467516661080084171061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95049956688881440112228081 71287467516661080084171061)
            ·
              refine ⟨6683200079686976257891037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71287467516661080084171061 6683200079686976257891037)
              ·
                refine ⟨2506200029882616096709139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683200079686976257891037 2506200029882616096709139)
                ·
                  refine ⟨3759300044823924145063709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506200029882616096709139 3759300044823924145063709)
                  ·
                    refine ⟨1409737516808971554398891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759300044823924145063709 1409737516808971554398891)
                    ·
                      rfl

theorem cell22_4118181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_4118181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118181 prefixEnd_4118181 := by exact prefixLift 4118181
  have htrace : WordTrace (prefixWord ++ tailWord_4118181) baseStart_4118181 baseEnd_4118181 := by
    simpa [prefixWord, tailWord_4118181, baseEnd_4118181] using wordTrace_append hprefix tailTrace_4118181
  have hstable : (prefixWord ++ tailWord_4118181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118181).length < 2 ^ (prefixWord ++ tailWord_4118181).sum := by decide
  have hdescent : baseEnd_4118181 < baseStart_4118181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118198 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4118198 : Nat := 118140960795 + 4118198 * 2 ^ 59
def prefixEnd_4118198 : Nat := 4983230072969 + 3 ^ 40 * 4118198 * 2
def baseEnd_4118198 : Nat := 1409743336256389176723839

theorem tailTrace_4118198 : CollatzResearch.WordTrace tailWord_4118198 prefixEnd_4118198 1409743336256389176723839 := by
  unfold tailWord_4118198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387688795904965816773203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100135347156319635378914165 9387688795904965816773203)
  ·
    refine ⟨14081533193857448725159805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9387688795904965816773203 14081533193857448725159805)
    ·
      refine ⟨5280574947696543271934927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14081533193857448725159805 5280574947696543271934927)
      ·
        refine ⟨7920862421544814907902391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280574947696543271934927 7920862421544814907902391)
        ·
          refine ⟨11881293632317222361853587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920862421544814907902391 11881293632317222361853587)
          ·
            refine ⟨17821940448475833542780381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881293632317222361853587 17821940448475833542780381)
            ·
              refine ⟨6683227668178437578542643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17821940448475833542780381 6683227668178437578542643)
              ·
                refine ⟨10024841502267656367813965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683227668178437578542643 10024841502267656367813965)
                ·
                  refine ⟨3759315563350371137930237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10024841502267656367813965 3759315563350371137930237)
                  ·
                    refine ⟨1409743336256389176723839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759315563350371137930237 1409743336256389176723839)
                    ·
                      rfl

theorem cell22_4118198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4118198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118198 prefixEnd_4118198 := by exact prefixLift 4118198
  have htrace : WordTrace (prefixWord ++ tailWord_4118198) baseStart_4118198 baseEnd_4118198 := by
    simpa [prefixWord, tailWord_4118198, baseEnd_4118198] using wordTrace_append hprefix tailTrace_4118198
  have hstable : (prefixWord ++ tailWord_4118198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118198).length < 2 ^ (prefixWord ++ tailWord_4118198).sum := by decide
  have hdescent : baseEnd_4118198 < baseStart_4118198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118207 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_4118207 : Nat := 118140960795 + 4118207 * 2 ^ 59
def prefixEnd_4118207 : Nat := 4983230072969 + 3 ^ 40 * 4118207 * 2
def baseEnd_4118207 : Nat := 1409746417140316153248811

theorem tailTrace_4118207 : CollatzResearch.WordTrace tailWord_4118207 prefixEnd_4118207 1409746417140316153248811 := by
  unfold tailWord_4118207
  simp only [CollatzResearch.WordTrace]
  refine ⟨150203348991446847605448875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100135565994297898403632583 150203348991446847605448875)
  ·
    refine ⟨225305023487170271408173313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150203348991446847605448875 225305023487170271408173313)
    ·
      refine ⟨168978767615377703556129985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225305023487170271408173313 168978767615377703556129985)
      ·
        refine ⟨126734075711533277667097489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168978767615377703556129985 126734075711533277667097489)
        ·
          refine ⟨95050556783649958250323117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126734075711533277667097489 95050556783649958250323117)
          ·
            refine ⟨35643958793868734343871169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95050556783649958250323117 35643958793868734343871169)
            ·
              refine ⟨26732969095401550757903377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35643958793868734343871169 26732969095401550757903377)
              ·
                refine ⟨20049726821551163068427533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26732969095401550757903377 20049726821551163068427533)
                ·
                  refine ⟨7518647558081686150660325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20049726821551163068427533 7518647558081686150660325)
                  ·
                    refine ⟨1409746417140316153248811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7518647558081686150660325 1409746417140316153248811)
                    ·
                      rfl

theorem cell22_4118207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_4118207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118207 prefixEnd_4118207 := by exact prefixLift 4118207
  have htrace : WordTrace (prefixWord ++ tailWord_4118207) baseStart_4118207 baseEnd_4118207 := by
    simpa [prefixWord, tailWord_4118207, baseEnd_4118207] using wordTrace_append hprefix tailTrace_4118207
  have hstable : (prefixWord ++ tailWord_4118207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118207).length < 2 ^ (prefixWord ++ tailWord_4118207).sum := by decide
  have hdescent : baseEnd_4118207 < baseStart_4118207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118222 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_4118222 : Nat := 118140960795 + 4118222 * 2 ^ 59
def prefixEnd_4118222 : Nat := 4983230072969 + 3 ^ 40 * 4118222 * 2
def baseEnd_4118222 : Nat := 469917183982287038041255

theorem tailTrace_4118222 : CollatzResearch.WordTrace tailWord_4118222 prefixEnd_4118222 469917183982287038041255 := by
  unfold tailWord_4118222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775487010799063145905615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100135930724261670111496613 18775487010799063145905615)
  ·
    refine ⟨28163230516198594718858423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18775487010799063145905615 28163230516198594718858423)
    ·
      refine ⟨42244845774297892078287635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28163230516198594718858423 42244845774297892078287635)
      ·
        refine ⟨63367268661446838117431453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42244845774297892078287635 63367268661446838117431453)
        ·
          refine ⟨23762725748042564294036795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63367268661446838117431453 23762725748042564294036795)
          ·
            refine ⟨35644088622063846441055193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23762725748042564294036795 35644088622063846441055193)
            ·
              refine ⟨26733066466547884830791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35644088622063846441055193 26733066466547884830791395)
              ·
                refine ⟨40099599699821827246187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26733066466547884830791395 40099599699821827246187093)
                ·
                  refine ⟨469917183982287038041255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40099599699821827246187093 469917183982287038041255)
                  ·
                    rfl

theorem cell22_4118222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_4118222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118222 prefixEnd_4118222 := by exact prefixLift 4118222
  have htrace : WordTrace (prefixWord ++ tailWord_4118222) baseStart_4118222 baseEnd_4118222 := by
    simpa [prefixWord, tailWord_4118222, baseEnd_4118222] using wordTrace_append hprefix tailTrace_4118222
  have hstable : (prefixWord ++ tailWord_4118222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118222).length < 2 ^ (prefixWord ++ tailWord_4118222).sum := by decide
  have hdescent : baseEnd_4118222 < baseStart_4118222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118239 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 4]
def baseStart_4118239 : Nat := 118140960795 + 4118239 * 2 ^ 59
def prefixEnd_4118239 : Nat := 4983230072969 + 3 ^ 40 * 4118239 * 2
def baseEnd_4118239 : Nat := 469919123798092912149571

theorem tailTrace_4118239 : CollatzResearch.WordTrace tailWord_4118239 prefixEnd_4118239 469919123798092912149571 := by
  unfold tailWord_4118239
  simp only [CollatzResearch.WordTrace]
  refine ⟨150204516127330917070613771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100136344084887278047075847 150204516127330917070613771)
  ·
    refine ⟨225306774190996375605920657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150204516127330917070613771 225306774190996375605920657)
    ·
      refine ⟨168980080643247281704440493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225306774190996375605920657 168980080643247281704440493)
      ·
        refine ⟨63367530241217730639165185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168980080643247281704440493 63367530241217730639165185)
        ·
          refine ⟨47525647680913297979373889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63367530241217730639165185 47525647680913297979373889)
          ·
            refine ⟨35644235760684973484530417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47525647680913297979373889 35644235760684973484530417)
            ·
              refine ⟨26733176820513730113397813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35644235760684973484530417 26733176820513730113397813)
              ·
                refine ⟨2506235326923162198131045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26733176820513730113397813 2506235326923162198131045)
                ·
                  refine ⟨469919123798092912149571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2506235326923162198131045 469919123798092912149571)
                  ·
                    rfl

theorem cell22_4118239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 4].length) (baseStart_4118239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118239 prefixEnd_4118239 := by exact prefixLift 4118239
  have htrace : WordTrace (prefixWord ++ tailWord_4118239) baseStart_4118239 baseEnd_4118239 := by
    simpa [prefixWord, tailWord_4118239, baseEnd_4118239] using wordTrace_append hprefix tailTrace_4118239
  have hstable : (prefixWord ++ tailWord_4118239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118239).length < 2 ^ (prefixWord ++ tailWord_4118239).sum := by decide
  have hdescent : baseEnd_4118239 < baseStart_4118239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118316 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_4118316 : Nat := 118140960795 + 4118316 * 2 ^ 59
def prefixEnd_4118316 : Nat := 4983230072969 + 3 ^ 40 * 4118316 * 2
def baseEnd_4118316 : Nat := 1409783730067876202273477

theorem tailTrace_4118316 : CollatzResearch.WordTrace tailWord_4118316 prefixEnd_4118316 1409783730067876202273477 := by
  unfold tailWord_4118316
  simp only [CollatzResearch.WordTrace]
  refine ⟨75103662274025979610583401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100138216365367972814111201 75103662274025979610583401)
  ·
    refine ⟨56327746705519484707937551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75103662274025979610583401 56327746705519484707937551)
    ·
      refine ⟨84491620058279227061906327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56327746705519484707937551 84491620058279227061906327)
      ·
        refine ⟨126737430087418840592859491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84491620058279227061906327 126737430087418840592859491)
        ·
          refine ⟨190106145131128260889289237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126737430087418840592859491 190106145131128260889289237)
          ·
            refine ⟨8911225553021637229185433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190106145131128260889289237 8911225553021637229185433)
            ·
              refine ⟨6683419164766227921889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911225553021637229185433 6683419164766227921889075)
              ·
                refine ⟨10025128747149341882833613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683419164766227921889075 10025128747149341882833613)
                ·
                  refine ⟨3759423280181003206062605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025128747149341882833613 3759423280181003206062605)
                  ·
                    refine ⟨1409783730067876202273477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759423280181003206062605 1409783730067876202273477)
                    ·
                      rfl

theorem cell22_4118316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_4118316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118316 prefixEnd_4118316 := by exact prefixLift 4118316
  have htrace : WordTrace (prefixWord ++ tailWord_4118316) baseStart_4118316 baseEnd_4118316 := by
    simpa [prefixWord, tailWord_4118316, baseEnd_4118316] using wordTrace_append hprefix tailTrace_4118316
  have hstable : (prefixWord ++ tailWord_4118316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118316).length < 2 ^ (prefixWord ++ tailWord_4118316).sum := by decide
  have hdescent : baseEnd_4118316 < baseStart_4118316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118327 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_4118327 : Nat := 118140960795 + 4118327 * 2 ^ 59
def prefixEnd_4118327 : Nat := 4983230072969 + 3 ^ 40 * 4118327 * 2
def baseEnd_4118327 : Nat := 1409787495592675840248443

theorem tailTrace_4118327 : CollatzResearch.WordTrace tailWord_4118327 prefixEnd_4118327 1409787495592675840248443 := by
  unfold tailWord_4118327
  simp only [CollatzResearch.WordTrace]
  refine ⟨150207725751012108099817235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100138483834008072066544823 150207725751012108099817235)
  ·
    refine ⟨225311588626518162149725853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150207725751012108099817235 225311588626518162149725853)
    ·
      refine ⟨84491845734944310806147195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225311588626518162149725853 84491845734944310806147195)
      ·
        refine ⟨126737768602416466209220793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84491845734944310806147195 126737768602416466209220793)
        ·
          refine ⟨95053326451812349656915595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126737768602416466209220793 95053326451812349656915595)
          ·
            refine ⟨142579989677718524485373393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95053326451812349656915595 142579989677718524485373393)
            ·
              refine ⟨106934992258288893364030045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142579989677718524485373393 106934992258288893364030045)
              ·
                refine ⟨40100622096858335011511267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106934992258288893364030045 40100622096858335011511267)
                ·
                  refine ⟨60150933145287502517266901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40100622096858335011511267 60150933145287502517266901)
                  ·
                    refine ⟨1409787495592675840248443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60150933145287502517266901 1409787495592675840248443)
                    ·
                      rfl

theorem cell22_4118327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_4118327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118327 prefixEnd_4118327 := by exact prefixLift 4118327
  have htrace : WordTrace (prefixWord ++ tailWord_4118327) baseStart_4118327 baseEnd_4118327 := by
    simpa [prefixWord, tailWord_4118327, baseEnd_4118327] using wordTrace_append hprefix tailTrace_4118327
  have hstable : (prefixWord ++ tailWord_4118327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118327).length < 2 ^ (prefixWord ++ tailWord_4118327).sum := by decide
  have hdescent : baseEnd_4118327 < baseStart_4118327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118404 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4118404 : Nat := 118140960795 + 4118404 * 2 ^ 59
def prefixEnd_4118404 : Nat := 4983230072969 + 3 ^ 40 * 4118404 * 2
def baseEnd_4118404 : Nat := 1409813854266273306073207

theorem tailTrace_4118404 : CollatzResearch.WordTrace tailWord_4118404 prefixEnd_4118404 1409813854266273306073207 := by
  unfold tailWord_4118404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75105267085866575125185133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100140356114488766833580177 75105267085866575125185133)
  ·
    refine ⟨28164475157199965671944425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75105267085866575125185133 28164475157199965671944425)
    ·
      refine ⟨21123356367899974253958319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28164475157199965671944425 21123356367899974253958319)
      ·
        refine ⟨31685034551849961380937479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21123356367899974253958319 31685034551849961380937479)
        ·
          refine ⟨47527551827774942071406219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31685034551849961380937479 47527551827774942071406219)
          ·
            refine ⟨71291327741662413107109329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47527551827774942071406219 71291327741662413107109329)
            ·
              refine ⟨53468495806246809830331997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71291327741662413107109329 53468495806246809830331997)
              ·
                refine ⟨20050685927342553686374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53468495806246809830331997 20050685927342553686374499)
                ·
                  refine ⟨30076028891013830529561749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20050685927342553686374499 30076028891013830529561749)
                  ·
                    refine ⟨1409813854266273306073207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30076028891013830529561749 1409813854266273306073207)
                    ·
                      rfl

theorem cell22_4118404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4118404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118404 prefixEnd_4118404 := by exact prefixLift 4118404
  have htrace : WordTrace (prefixWord ++ tailWord_4118404) baseStart_4118404 baseEnd_4118404 := by
    simpa [prefixWord, tailWord_4118404, baseEnd_4118404] using wordTrace_append hprefix tailTrace_4118404
  have hstable : (prefixWord ++ tailWord_4118404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118404).length < 2 ^ (prefixWord ++ tailWord_4118404).sum := by decide
  have hdescent : baseEnd_4118404 < baseStart_4118404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118410 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_4118410 : Nat := 118140960795 + 4118410 * 2 ^ 59
def prefixEnd_4118410 : Nat := 4983230072969 + 3 ^ 40 * 4118410 * 2
def baseEnd_4118410 : Nat := 1409815908188891290423189

theorem tailTrace_4118410 : CollatzResearch.WordTrace tailWord_4118410 prefixEnd_4118410 1409815908188891290423189 := by
  unfold tailWord_4118410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37552688252427853318772171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100140502006474275516725789 37552688252427853318772171)
  ·
    refine ⟨56329032378641779978158257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37552688252427853318772171 56329032378641779978158257)
    ·
      refine ⟨42246774283981334983618693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56329032378641779978158257 42246774283981334983618693)
      ·
        refine ⟨7921270178246500309428505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42246774283981334983618693 7921270178246500309428505)
        ·
          refine ⟨5940952633684875232071379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921270178246500309428505 5940952633684875232071379)
          ·
            refine ⟨8911428950527312848107069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940952633684875232071379 8911428950527312848107069)
            ·
              refine ⟨3341785856447742318040151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8911428950527312848107069 3341785856447742318040151)
              ·
                refine ⟨5012678784671613477060227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341785856447742318040151 5012678784671613477060227)
                ·
                  refine ⟨7519018177007420215590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012678784671613477060227 7519018177007420215590341)
                  ·
                    refine ⟨1409815908188891290423189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519018177007420215590341 1409815908188891290423189)
                    ·
                      rfl

theorem cell22_4118410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_4118410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118410 prefixEnd_4118410 := by exact prefixLift 4118410
  have htrace : WordTrace (prefixWord ++ tailWord_4118410) baseStart_4118410 baseEnd_4118410 := by
    simpa [prefixWord, tailWord_4118410, baseEnd_4118410] using wordTrace_append hprefix tailTrace_4118410
  have hstable : (prefixWord ++ tailWord_4118410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118410).length < 2 ^ (prefixWord ++ tailWord_4118410).sum := by decide
  have hdescent : baseEnd_4118410 < baseStart_4118410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118423 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 2, 3]
def baseStart_4118423 : Nat := 118140960795 + 4118423 * 2 ^ 59
def prefixEnd_4118423 : Nat := 4983230072969 + 3 ^ 40 * 4118423 * 2
def baseEnd_4118423 : Nat := 1409820358354563589848149

theorem tailTrace_4118423 : CollatzResearch.WordTrace tailWord_4118423 prefixEnd_4118423 1409820358354563589848149 := by
  unfold tailWord_4118423
  simp only [CollatzResearch.WordTrace]
  refine ⟨150211227158664316495311923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100140818105776210996874615 150211227158664316495311923)
  ·
    refine ⟨225316840737996474742967885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150211227158664316495311923 225316840737996474742967885)
    ·
      refine ⟨84493815276748678028612957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225316840737996474742967885 84493815276748678028612957)
      ·
        refine ⟨31685180728780754260729859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84493815276748678028612957 31685180728780754260729859)
        ·
          refine ⟨47527771093171131391094789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31685180728780754260729859 47527771093171131391094789)
          ·
            refine ⟨8911457079969587135830273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47527771093171131391094789 8911457079969587135830273)
            ·
              refine ⟨6683592809977190351872705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911457079969587135830273 6683592809977190351872705)
              ·
                refine ⟨5012694607482892763904529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6683592809977190351872705 5012694607482892763904529)
                ·
                  refine ⟨3759520955612169572928397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012694607482892763904529 3759520955612169572928397)
                  ·
                    refine ⟨1409820358354563589848149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759520955612169572928397 1409820358354563589848149)
                    ·
                      rfl

theorem cell22_4118423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_4118423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118423 prefixEnd_4118423 := by exact prefixLift 4118423
  have htrace : WordTrace (prefixWord ++ tailWord_4118423) baseStart_4118423 baseEnd_4118423 := by
    simpa [prefixWord, tailWord_4118423, baseEnd_4118423] using wordTrace_append hprefix tailTrace_4118423
  have hstable : (prefixWord ++ tailWord_4118423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118423).length < 2 ^ (prefixWord ++ tailWord_4118423).sum := by decide
  have hdescent : baseEnd_4118423 < baseStart_4118423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118436 : List Nat := [2, 3, 1, 2, 1, 5, 1, 7]
def baseStart_4118436 : Nat := 118140960795 + 4118436 * 2 ^ 59
def prefixEnd_4118436 : Nat := 4983230072969 + 3 ^ 40 * 4118436 * 2
def baseEnd_4118436 : Nat := 156647200946692876585901

theorem tailTrace_4118436 : CollatzResearch.WordTrace tailWord_4118436 prefixEnd_4118436 156647200946692876585901 := by
  unfold tailWord_4118436
  simp only [CollatzResearch.WordTrace]
  refine ⟨75105850653808609857767581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100141134205078146477023441 75105850653808609857767581)
  ·
    refine ⟨28164693995178228696662843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75105850653808609857767581 28164693995178228696662843)
    ·
      refine ⟨42247040992767343044994265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28164693995178228696662843 42247040992767343044994265)
      ·
        refine ⟨31685280744575507283745699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42247040992767343044994265 31685280744575507283745699)
        ·
          refine ⟨47527921116863260925618549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31685280744575507283745699 47527921116863260925618549)
          ·
            refine ⟨4455742604705930711776739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47527921116863260925618549 4455742604705930711776739)
            ·
              refine ⟨6683613907058896067665109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455742604705930711776739 6683613907058896067665109)
              ·
                refine ⟨156647200946692876585901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6683613907058896067665109 156647200946692876585901)
                ·
                  rfl

theorem cell22_4118436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_4118436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118436 prefixEnd_4118436 := by exact prefixLift 4118436
  have htrace : WordTrace (prefixWord ++ tailWord_4118436) baseStart_4118436 baseEnd_4118436 := by
    simpa [prefixWord, tailWord_4118436, baseEnd_4118436] using wordTrace_append hprefix tailTrace_4118436
  have hstable : (prefixWord ++ tailWord_4118436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118436).length < 2 ^ (prefixWord ++ tailWord_4118436).sum := by decide
  have hdescent : baseEnd_4118436 < baseStart_4118436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118440 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4118440 : Nat := 118140960795 + 4118440 * 2 ^ 59
def prefixEnd_4118440 : Nat := 4983230072969 + 3 ^ 40 * 4118440 * 2
def baseEnd_4118440 : Nat := 1409826177801981212173097

theorem tailTrace_4118440 : CollatzResearch.WordTrace tailWord_4118440 prefixEnd_4118440 1409826177801981212173097 := by
  unfold tailWord_4118440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75105923599801364199340387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100141231466401818932453849 75105923599801364199340387)
  ·
    refine ⟨112658885399702046299010581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75105923599801364199340387 112658885399702046299010581)
    ·
      refine ⟨5280885253111033420266121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112658885399702046299010581 5280885253111033420266121)
      ·
        refine ⟨3960663939833275065199591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5280885253111033420266121 3960663939833275065199591)
        ·
          refine ⟨5940995909749912597799387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960663939833275065199591 5940995909749912597799387)
          ·
            refine ⟨8911493864624868896699081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940995909749912597799387 8911493864624868896699081)
            ·
              refine ⟨6683620398468651672524311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911493864624868896699081 6683620398468651672524311)
              ·
                refine ⟨10025430597702977508786467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683620398468651672524311 10025430597702977508786467)
                ·
                  refine ⟨15038145896554466263179701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10025430597702977508786467 15038145896554466263179701)
                  ·
                    refine ⟨1409826177801981212173097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15038145896554466263179701 1409826177801981212173097)
                    ·
                      rfl

theorem cell22_4118440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4118440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118440 prefixEnd_4118440 := by exact prefixLift 4118440
  have htrace : WordTrace (prefixWord ++ tailWord_4118440) baseStart_4118440 baseEnd_4118440 := by
    simpa [prefixWord, tailWord_4118440, baseEnd_4118440] using wordTrace_append hprefix tailTrace_4118440
  have hstable : (prefixWord ++ tailWord_4118440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118440).length < 2 ^ (prefixWord ++ tailWord_4118440).sum := by decide
  have hdescent : baseEnd_4118440 < baseStart_4118440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118451 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 3, 3]
def baseStart_4118451 : Nat := 118140960795 + 4118451 * 2 ^ 59
def prefixEnd_4118451 : Nat := 4983230072969 + 3 ^ 40 * 4118451 * 2
def baseEnd_4118451 : Nat := 1409829943326780850148063

theorem tailTrace_4118451 : CollatzResearch.WordTrace tailWord_4118451 prefixEnd_4118451 1409829943326780850148063 := by
  unfold tailWord_4118451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150212248402562877277331207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100141498935041918184887471 150212248402562877277331207)
  ·
    refine ⟨225318372603844315915996811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150212248402562877277331207 225318372603844315915996811)
    ·
      refine ⟨337977558905766473873995217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225318372603844315915996811 337977558905766473873995217)
      ·
        refine ⟨253483169179324855405496413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337977558905766473873995217 253483169179324855405496413)
        ·
          refine ⟨95056188442246820777061155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253483169179324855405496413 95056188442246820777061155)
          ·
            refine ⟨142584282663370231165591733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95056188442246820777061155 142584282663370231165591733)
            ·
              refine ⟨13367276499690959171774225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142584282663370231165591733 13367276499690959171774225)
              ·
                refine ⟨10025457374768219378830669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13367276499690959171774225 10025457374768219378830669)
                ·
                  refine ⟨3759546515538082267061501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025457374768219378830669 3759546515538082267061501)
                  ·
                    refine ⟨1409829943326780850148063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759546515538082267061501 1409829943326780850148063)
                    ·
                      rfl

theorem cell22_4118451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].length) (baseStart_4118451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118451 prefixEnd_4118451 := by exact prefixLift 4118451
  have htrace : WordTrace (prefixWord ++ tailWord_4118451) baseStart_4118451 baseEnd_4118451 := by
    simpa [prefixWord, tailWord_4118451, baseEnd_4118451] using wordTrace_append hprefix tailTrace_4118451
  have hstable : (prefixWord ++ tailWord_4118451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118451).length < 2 ^ (prefixWord ++ tailWord_4118451).sum := by decide
  have hdescent : baseEnd_4118451 < baseStart_4118451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118464 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_4118464 : Nat := 118140960795 + 4118464 * 2 ^ 59
def prefixEnd_4118464 : Nat := 4983230072969 + 3 ^ 40 * 4118464 * 2
def baseEnd_4118464 : Nat := 469944797830817716524341

theorem tailTrace_4118464 : CollatzResearch.WordTrace tailWord_4118464 prefixEnd_4118464 469944797830817716524341 := by
  unfold tailWord_4118464
  simp only [CollatzResearch.WordTrace]
  refine ⟨75106361275757890248777223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100141815034343853665036297 75106361275757890248777223)
  ·
    refine ⟨112659541913636835373165835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75106361275757890248777223 112659541913636835373165835)
    ·
      refine ⟨168989312870455253059748753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112659541913636835373165835 168989312870455253059748753)
      ·
        refine ⟨126741984652841439794811565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168989312870455253059748753 126741984652841439794811565)
        ·
          refine ⟨47528244244815539923054337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126741984652841439794811565 47528244244815539923054337)
          ·
            refine ⟨35646183183611654942290753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47528244244815539923054337 35646183183611654942290753)
            ·
              refine ⟨26734637387708741206718065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35646183183611654942290753 26734637387708741206718065)
              ·
                refine ⟨20050978040781555905038549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26734637387708741206718065 20050978040781555905038549)
                ·
                  refine ⟨469944797830817716524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20050978040781555905038549 469944797830817716524341)
                  ·
                    rfl

theorem cell22_4118464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_4118464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118464 prefixEnd_4118464 := by exact prefixLift 4118464
  have htrace : WordTrace (prefixWord ++ tailWord_4118464) baseStart_4118464 baseEnd_4118464 := by
    simpa [prefixWord, tailWord_4118464, baseEnd_4118464] using wordTrace_append hprefix tailTrace_4118464
  have hstable : (prefixWord ++ tailWord_4118464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118464).length < 2 ^ (prefixWord ++ tailWord_4118464).sum := by decide
  have hdescent : baseEnd_4118464 < baseStart_4118464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118479 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_4118479 : Nat := 118140960795 + 4118479 * 2 ^ 59
def prefixEnd_4118479 : Nat := 4983230072969 + 3 ^ 40 * 4118479 * 2
def baseEnd_4118479 : Nat := 1409839528298998110447977

theorem tailTrace_4118479 : CollatzResearch.WordTrace tailWord_4118479 prefixEnd_4118479 1409839528298998110447977 := by
  unfold tailWord_4118479
  simp only [CollatzResearch.WordTrace]
  refine ⟨150213269646461438059350491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100142179764307625372900327 150213269646461438059350491)
  ·
    refine ⟨225319904469692157089025737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150213269646461438059350491 225319904469692157089025737)
    ·
      refine ⟨168989928352269117816769303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225319904469692157089025737 168989928352269117816769303)
      ·
        refine ⟨253484892528403676725153955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168989928352269117816769303 253484892528403676725153955)
        ·
          refine ⟨380227338792605515087730933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253484892528403676725153955 380227338792605515087730933)
          ·
            refine ⟨35646313011806767039474775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380227338792605515087730933 35646313011806767039474775)
            ·
              refine ⟨53469469517710150559212163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35646313011806767039474775 53469469517710150559212163)
              ·
                refine ⟨80204204276565225838818245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53469469517710150559212163 80204204276565225838818245)
                ·
                  refine ⟨15038288301855979844778421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80204204276565225838818245 15038288301855979844778421)
                  ·
                    refine ⟨1409839528298998110447977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15038288301855979844778421 1409839528298998110447977)
                    ·
                      rfl

theorem cell22_4118479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_4118479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118479 prefixEnd_4118479 := by exact prefixLift 4118479
  have htrace : WordTrace (prefixWord ++ tailWord_4118479) baseStart_4118479 baseEnd_4118479 := by
    simpa [prefixWord, tailWord_4118479, baseEnd_4118479] using wordTrace_append hprefix tailTrace_4118479
  have hstable : (prefixWord ++ tailWord_4118479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118479).length < 2 ^ (prefixWord ++ tailWord_4118479).sum := by decide
  have hdescent : baseEnd_4118479 < baseStart_4118479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118485 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_4118485 : Nat := 118140960795 + 4118485 * 2 ^ 59
def prefixEnd_4118485 : Nat := 4983230072969 + 3 ^ 40 * 4118485 * 2
def baseEnd_4118485 : Nat := 1409841582221616094797959

theorem tailTrace_4118485 : CollatzResearch.WordTrace tailWord_4118485 prefixEnd_4118485 1409841582221616094797959 := by
  unfold tailWord_4118485
  simp only [CollatzResearch.WordTrace]
  refine ⟨150213488484439701084068909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100142325656293134056045939 150213488484439701084068909)
  ·
    refine ⟨56330058181664887906525841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150213488484439701084068909 56330058181664887906525841)
    ·
      refine ⟨42247543636248665929894381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56330058181664887906525841 42247543636248665929894381)
      ·
        refine ⟨15842828863593249723710393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42247543636248665929894381 15842828863593249723710393)
        ·
          refine ⟨11882121647694937292782795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15842828863593249723710393 11882121647694937292782795)
          ·
            refine ⟨17823182471542405939174193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882121647694937292782795 17823182471542405939174193)
            ·
              refine ⟨13367386853656804454380645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17823182471542405939174193 13367386853656804454380645)
              ·
                refine ⟨2506385035060650835196371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13367386853656804454380645 2506385035060650835196371)
                ·
                  refine ⟨3759577552590976252794557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506385035060650835196371 3759577552590976252794557)
                  ·
                    refine ⟨1409841582221616094797959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759577552590976252794557 1409841582221616094797959)
                    ·
                      rfl

theorem cell22_4118485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_4118485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118485 prefixEnd_4118485 := by exact prefixLift 4118485
  have htrace : WordTrace (prefixWord ++ tailWord_4118485) baseStart_4118485 baseEnd_4118485 := by
    simpa [prefixWord, tailWord_4118485, baseEnd_4118485] using wordTrace_append hprefix tailTrace_4118485
  have hstable : (prefixWord ++ tailWord_4118485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118485).length < 2 ^ (prefixWord ++ tailWord_4118485).sum := by decide
  have hdescent : baseEnd_4118485 < baseStart_4118485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118620 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_4118620 : Nat := 118140960795 + 4118620 * 2 ^ 59
def prefixEnd_4118620 : Nat := 4983230072969 + 3 ^ 40 * 4118620 * 2
def baseEnd_4118620 : Nat := 1409887795480520742672545

theorem tailTrace_4118620 : CollatzResearch.WordTrace tailWord_4118620 prefixEnd_4118620 1409887795480520742672545 := by
  unfold tailWord_4118620
  simp only [CollatzResearch.WordTrace]
  refine ⟨75109206169475309570116657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100145608225967079426822209 75109206169475309570116657)
  ·
    refine ⟨56331904627106482177587493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75109206169475309570116657 56331904627106482177587493)
    ·
      refine ⟨10562232117582465408297655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56331904627106482177587493 10562232117582465408297655)
      ·
        refine ⟨15843348176373698112446483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10562232117582465408297655 15843348176373698112446483)
        ·
          refine ⟨23765022264560547168669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15843348176373698112446483 23765022264560547168669725)
          ·
            refine ⟨8911883349210205188251147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23765022264560547168669725 8911883349210205188251147)
            ·
              refine ⟨13367825023815307782376721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911883349210205188251147 13367825023815307782376721)
              ·
                refine ⟨10025868767861480836782541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13367825023815307782376721 10025868767861480836782541)
                ·
                  refine ⟨3759700787948055313793453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025868767861480836782541 3759700787948055313793453)
                  ·
                    refine ⟨1409887795480520742672545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759700787948055313793453 1409887795480520742672545)
                    ·
                      rfl

theorem cell22_4118620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_4118620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118620 prefixEnd_4118620 := by exact prefixLift 4118620
  have htrace : WordTrace (prefixWord ++ tailWord_4118620) baseStart_4118620 baseEnd_4118620 := by
    simpa [prefixWord, tailWord_4118620, baseEnd_4118620] using wordTrace_append hprefix tailTrace_4118620
  have hstable : (prefixWord ++ tailWord_4118620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118620).length < 2 ^ (prefixWord ++ tailWord_4118620).sum := by decide
  have hdescent : baseEnd_4118620 < baseStart_4118620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118631 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4118631 : Nat := 118140960795 + 4118631 * 2 ^ 59
def prefixEnd_4118631 : Nat := 4983230072969 + 3 ^ 40 * 4118631 * 2
def baseEnd_4118631 : Nat := 1409891561005320380647511

theorem tailTrace_4118631 : CollatzResearch.WordTrace tailWord_4118631 prefixEnd_4118631 1409891561005320380647511 := by
  unfold tailWord_4118631
  simp only [CollatzResearch.WordTrace]
  refine ⟨150218813541910768018883747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100145875694607178679255831 150218813541910768018883747)
  ·
    refine ⟨225328220312866152028325621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150218813541910768018883747 225328220312866152028325621)
    ·
      refine ⟨21124520654331201752655527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225328220312866152028325621 21124520654331201752655527)
      ·
        refine ⟨31686780981496802628983291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124520654331201752655527 31686780981496802628983291)
        ·
          refine ⟨47530171472245203943474937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686780981496802628983291 47530171472245203943474937)
          ·
            refine ⟨35647628604183902957606203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47530171472245203943474937 35647628604183902957606203)
            ·
              refine ⟨53471442906275854436409305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35647628604183902957606203 53471442906275854436409305)
              ·
                refine ⟨40103582179706890827306979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53471442906275854436409305 40103582179706890827306979)
                ·
                  refine ⟨60155373269560336240960469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40103582179706890827306979 60155373269560336240960469)
                  ·
                    refine ⟨1409891561005320380647511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60155373269560336240960469 1409891561005320380647511)
                    ·
                      rfl

theorem cell22_4118631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4118631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118631 prefixEnd_4118631 := by exact prefixLift 4118631
  have htrace : WordTrace (prefixWord ++ tailWord_4118631) baseStart_4118631 baseEnd_4118631 := by
    simpa [prefixWord, tailWord_4118631, baseEnd_4118631] using wordTrace_append hprefix tailTrace_4118631
  have hstable : (prefixWord ++ tailWord_4118631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118631).length < 2 ^ (prefixWord ++ tailWord_4118631).sum := by decide
  have hdescent : baseEnd_4118631 < baseStart_4118631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118637 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_4118637 : Nat := 118140960795 + 4118637 * 2 ^ 59
def prefixEnd_4118637 : Nat := 4983230072969 + 3 ^ 40 * 4118637 * 2
def baseEnd_4118637 : Nat := 1409893614927938364997493

theorem tailTrace_4118637 : CollatzResearch.WordTrace tailWord_4118637 prefixEnd_4118637 1409893614927938364997493 := by
  unfold tailWord_4118637
  simp only [CollatzResearch.WordTrace]
  refine ⟨150219032379889031043602165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100146021586592687362401443 150219032379889031043602165)
  ·
    refine ⟨14083034285614596660337703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150219032379889031043602165 14083034285614596660337703)
    ·
      refine ⟨21124551428421894990506555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14083034285614596660337703 21124551428421894990506555)
      ·
        refine ⟨31686827142632842485759833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124551428421894990506555 31686827142632842485759833)
        ·
          refine ⟨23765120356974631864319875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31686827142632842485759833 23765120356974631864319875)
          ·
            refine ⟨35647680535461947796479813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23765120356974631864319875 35647680535461947796479813)
            ·
              refine ⟨6683940100399115211839965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35647680535461947796479813 6683940100399115211839965)
              ·
                refine ⟨2506477537649668204439987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683940100399115211839965 2506477537649668204439987)
                ·
                  refine ⟨3759716306474502306659981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506477537649668204439987 3759716306474502306659981)
                  ·
                    refine ⟨1409893614927938364997493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759716306474502306659981 1409893614927938364997493)
                    ·
                      rfl

theorem cell22_4118637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_4118637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118637 prefixEnd_4118637 := by exact prefixLift 4118637
  have htrace : WordTrace (prefixWord ++ tailWord_4118637) baseStart_4118637 baseEnd_4118637 := by
    simpa [prefixWord, tailWord_4118637, baseEnd_4118637] using wordTrace_append hprefix tailTrace_4118637
  have hstable : (prefixWord ++ tailWord_4118637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118637).length < 2 ^ (prefixWord ++ tailWord_4118637).sum := by decide
  have hdescent : baseEnd_4118637 < baseStart_4118637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118693 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_4118693 : Nat := 118140960795 + 4118693 * 2 ^ 59
def prefixEnd_4118693 : Nat := 4983230072969 + 3 ^ 40 * 4118693 * 2
def baseEnd_4118693 : Nat := 1409912784872372885597321

theorem tailTrace_4118693 : CollatzResearch.WordTrace tailWord_4118693 prefixEnd_4118693 1409912784872372885597321 := by
  unfold tailWord_4118693
  simp only [CollatzResearch.WordTrace]
  refine ⟨150221074867686152607640733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100147383245124101738427155 150221074867686152607640733)
  ·
    refine ⟨56332903075382307227865275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150221074867686152607640733 56332903075382307227865275)
    ·
      refine ⟨84499354613073460841797913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56332903075382307227865275 84499354613073460841797913)
      ·
        refine ⟨63374515959805095631348435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84499354613073460841797913 63374515959805095631348435)
        ·
          refine ⟨95061773939707643447022653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63374515959805095631348435 95061773939707643447022653)
          ·
            refine ⟨35648165227390366292633495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95061773939707643447022653 35648165227390366292633495)
            ·
              refine ⟨53472247841085549438950243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35648165227390366292633495 53472247841085549438950243)
              ·
                refine ⟨80208371761628324158425365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53472247841085549438950243 80208371761628324158425365)
                ·
                  refine ⟨3759767426326327694926189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80208371761628324158425365 3759767426326327694926189)
                  ·
                    refine ⟨1409912784872372885597321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759767426326327694926189 1409912784872372885597321)
                    ·
                      rfl

theorem cell22_4118693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_4118693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118693 prefixEnd_4118693 := by exact prefixLift 4118693
  have htrace : WordTrace (prefixWord ++ tailWord_4118693) baseStart_4118693 baseEnd_4118693 := by
    simpa [prefixWord, tailWord_4118693, baseEnd_4118693] using wordTrace_append hprefix tailTrace_4118693
  have hstable : (prefixWord ++ tailWord_4118693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118693).length < 2 ^ (prefixWord ++ tailWord_4118693).sum := by decide
  have hdescent : baseEnd_4118693 < baseStart_4118693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118742 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4118742 : Nat := 118140960795 + 4118742 * 2 ^ 59
def prefixEnd_4118742 : Nat := 4983230072969 + 3 ^ 40 * 4118742 * 2
def baseEnd_4118742 : Nat := 1409929558573753091122171

theorem tailTrace_4118742 : CollatzResearch.WordTrace tailWord_4118742 prefixEnd_4118742 1409929558573753091122171 := by
  unfold tailWord_4118742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388928877781789623510905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100148574696339089317449653 9388928877781789623510905)
  ·
    refine ⟨7041696658336342217633179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9388928877781789623510905 7041696658336342217633179)
    ·
      refine ⟨10562544987504513326449769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7041696658336342217633179 10562544987504513326449769)
      ·
        refine ⟨7921908740628384994837327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10562544987504513326449769 7921908740628384994837327)
        ·
          refine ⟨11882863110942577492255991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7921908740628384994837327 11882863110942577492255991)
          ·
            refine ⟨17824294666413866238383987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882863110942577492255991 17824294666413866238383987)
            ·
              refine ⟨26736441999620799357575981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824294666413866238383987 26736441999620799357575981)
              ·
                refine ⟨10026165749857799759090993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26736441999620799357575981 10026165749857799759090993)
                ·
                  refine ⟨7519624312393349819318245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10026165749857799759090993 7519624312393349819318245)
                  ·
                    refine ⟨1409929558573753091122171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519624312393349819318245 1409929558573753091122171)
                    ·
                      rfl

theorem cell22_4118742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4118742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118742 prefixEnd_4118742 := by exact prefixLift 4118742
  have htrace : WordTrace (prefixWord ++ tailWord_4118742) baseStart_4118742 baseEnd_4118742 := by
    simpa [prefixWord, tailWord_4118742, baseEnd_4118742] using wordTrace_append hprefix tailTrace_4118742
  have hstable : (prefixWord ++ tailWord_4118742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118742).length < 2 ^ (prefixWord ++ tailWord_4118742).sum := by decide
  have hdescent : baseEnd_4118742 < baseStart_4118742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118783 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_4118783 : Nat := 118140960795 + 4118783 * 2 ^ 59
def prefixEnd_4118783 : Nat := 4983230072969 + 3 ^ 40 * 4118783 * 2
def baseEnd_4118783 : Nat := 1409943593711642650847045

theorem tailTrace_4118783 : CollatzResearch.WordTrace tailWord_4118783 prefixEnd_4118783 1409943593711642650847045 := by
  unfold tailWord_4118783
  simp only [CollatzResearch.WordTrace]
  refine ⟨150224357437360097978417003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100149571624906731985611335 150224357437360097978417003)
  ·
    refine ⟨225336536156040146967625505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150224357437360097978417003 225336536156040146967625505)
    ·
      refine ⟨169002402117030110225719129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225336536156040146967625505 169002402117030110225719129)
      ·
        refine ⟨126751801587772582669289347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169002402117030110225719129 126751801587772582669289347)
        ·
          refine ⟨190127702381658874003934021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126751801587772582669289347 190127702381658874003934021)
          ·
            refine ⟨35648944196561038875737629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190127702381658874003934021 35648944196561038875737629)
            ·
              refine ⟨13368354073710389578401611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35648944196561038875737629 13368354073710389578401611)
              ·
                refine ⟨20052531110565584367602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13368354073710389578401611 20052531110565584367602417)
                ·
                  refine ⟨15039398332924188275701813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20052531110565584367602417 15039398332924188275701813)
                  ·
                    refine ⟨1409943593711642650847045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15039398332924188275701813 1409943593711642650847045)
                    ·
                      rfl

theorem cell22_4118783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_4118783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118783 prefixEnd_4118783 := by exact prefixLift 4118783
  have htrace : WordTrace (prefixWord ++ tailWord_4118783) baseStart_4118783 baseEnd_4118783 := by
    simpa [prefixWord, tailWord_4118783, baseEnd_4118783] using wordTrace_append hprefix tailTrace_4118783
  have hstable : (prefixWord ++ tailWord_4118783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118783).length < 2 ^ (prefixWord ++ tailWord_4118783).sum := by decide
  have hdescent : baseEnd_4118783 < baseStart_4118783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118828 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4118828 : Nat := 118140960795 + 4118828 * 2 ^ 59
def prefixEnd_4118828 : Nat := 4983230072969 + 3 ^ 40 * 4118828 * 2
def baseEnd_4118828 : Nat := 1409958998131277533471907

theorem tailTrace_4118828 : CollatzResearch.WordTrace tailWord_4118828 prefixEnd_4118828 1409958998131277533471907 := by
  unfold tailWord_4118828
  simp only [CollatzResearch.WordTrace]
  refine ⟨75112999361098535331902569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100150665814798047109203425 75112999361098535331902569)
  ·
    refine ⟨56334749520823901498926927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75112999361098535331902569 56334749520823901498926927)
    ·
      refine ⟨84502124281235852248390391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56334749520823901498926927 84502124281235852248390391)
      ·
        refine ⟨126753186421853778372585587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84502124281235852248390391 126753186421853778372585587)
        ·
          refine ⟨190129779632780667558878381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126753186421853778372585587 190129779632780667558878381)
          ·
            refine ⟨71298667362292750334579393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190129779632780667558878381 71298667362292750334579393)
            ·
              refine ⟨53474000521719562750934545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71298667362292750334579393 53474000521719562750934545)
              ·
                refine ⟨40105500391289672063200909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53474000521719562750934545 40105500391289672063200909)
                ·
                  refine ⟨15039562646733627023700341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40105500391289672063200909 15039562646733627023700341)
                  ·
                    refine ⟨1409958998131277533471907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15039562646733627023700341 1409958998131277533471907)
                    ·
                      rfl

theorem cell22_4118828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4118828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118828 prefixEnd_4118828 := by exact prefixLift 4118828
  have htrace : WordTrace (prefixWord ++ tailWord_4118828) baseStart_4118828 baseEnd_4118828 := by
    simpa [prefixWord, tailWord_4118828, baseEnd_4118828] using wordTrace_append hprefix tailTrace_4118828
  have hstable : (prefixWord ++ tailWord_4118828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118828).length < 2 ^ (prefixWord ++ tailWord_4118828).sum := by decide
  have hdescent : baseEnd_4118828 < baseStart_4118828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118849 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4118849 : Nat := 118140960795 + 4118849 * 2 ^ 59
def prefixEnd_4118849 : Nat := 4983230072969 + 3 ^ 40 * 4118849 * 2
def baseEnd_4118849 : Nat := 1409966186860440478696843

theorem tailTrace_4118849 : CollatzResearch.WordTrace tailWord_4118849 prefixEnd_4118849 1409966186860440478696843 := by
  unfold tailWord_4118849
  simp only [CollatzResearch.WordTrace]
  refine ⟨150226764655120991250319601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100151176436747327500213067 150226764655120991250319601)
  ·
    refine ⟨112670073491340743437739701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150226764655120991250319601 112670073491340743437739701)
    ·
      refine ⟨10562819389813194697288097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112670073491340743437739701 10562819389813194697288097)
      ·
        refine ⟨7922114542359896022966073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10562819389813194697288097 7922114542359896022966073)
        ·
          refine ⟨5941585906769922017224555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7922114542359896022966073 5941585906769922017224555)
          ·
            refine ⟨8912378860154883025836833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941585906769922017224555 8912378860154883025836833)
            ·
              refine ⟨6684284145116162269377625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8912378860154883025836833 6684284145116162269377625)
              ·
                refine ⟨5013213108837121702033219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684284145116162269377625 5013213108837121702033219)
                ·
                  refine ⟨7519819663255682553049829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013213108837121702033219 7519819663255682553049829)
                  ·
                    refine ⟨1409966186860440478696843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519819663255682553049829 1409966186860440478696843)
                    ·
                      rfl

theorem cell22_4118849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4118849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118849 prefixEnd_4118849 := by exact prefixLift 4118849
  have htrace : WordTrace (prefixWord ++ tailWord_4118849) baseStart_4118849 baseEnd_4118849 := by
    simpa [prefixWord, tailWord_4118849, baseEnd_4118849] using wordTrace_append hprefix tailTrace_4118849
  have hstable : (prefixWord ++ tailWord_4118849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118849).length < 2 ^ (prefixWord ++ tailWord_4118849).sum := by decide
  have hdescent : baseEnd_4118849 < baseStart_4118849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118860 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_4118860 : Nat := 118140960795 + 4118860 * 2 ^ 59
def prefixEnd_4118860 : Nat := 4983230072969 + 3 ^ 40 * 4118860 * 2
def baseEnd_4118860 : Nat := 1409969952385240116671809

theorem tailTrace_4118860 : CollatzResearch.WordTrace tailWord_4118860 prefixEnd_4118860 1409969952385240116671809 := by
  unfold tailWord_4118860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75113582929040570064485017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100151443905387426752646689 75113582929040570064485017)
  ·
    refine ⟨56335187196780427548363763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75113582929040570064485017 56335187196780427548363763)
    ·
      refine ⟨84502780795170641322545645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56335187196780427548363763 84502780795170641322545645)
      ·
        refine ⟨31688542798188990495954617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84502780795170641322545645 31688542798188990495954617)
        ·
          refine ⟨23766407098641742871965963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31688542798188990495954617 23766407098641742871965963)
          ·
            refine ⟨35649610647962614307948945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23766407098641742871965963 35649610647962614307948945)
            ·
              refine ⟨26737207985971960730961709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35649610647962614307948945 26737207985971960730961709)
              ·
                refine ⟨10026452994739485274110641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26737207985971960730961709 10026452994739485274110641)
                ·
                  refine ⟨7519839746054613955582981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10026452994739485274110641 7519839746054613955582981)
                  ·
                    refine ⟨1409969952385240116671809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519839746054613955582981 1409969952385240116671809)
                    ·
                      rfl

theorem cell22_4118860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_4118860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118860 prefixEnd_4118860 := by exact prefixLift 4118860
  have htrace : WordTrace (prefixWord ++ tailWord_4118860) baseStart_4118860 baseEnd_4118860 := by
    simpa [prefixWord, tailWord_4118860, baseEnd_4118860] using wordTrace_append hprefix tailTrace_4118860
  have hstable : (prefixWord ++ tailWord_4118860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118860).length < 2 ^ (prefixWord ++ tailWord_4118860).sum := by decide
  have hdescent : baseEnd_4118860 < baseStart_4118860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118903 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 9]
def baseStart_4118903 : Nat := 118140960795 + 4118903 * 2 ^ 59
def prefixEnd_4118903 : Nat := 4983230072969 + 3 ^ 40 * 4118903 * 2
def baseEnd_4118903 : Nat := 469994890721334112615559

theorem tailTrace_4118903 : CollatzResearch.WordTrace tailWord_4118903 prefixEnd_4118903 469994890721334112615559 := by
  unfold tailWord_4118903
  simp only [CollatzResearch.WordTrace]
  refine ⟨150228734196925358472785363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100152489464616905648523575 150228734196925358472785363)
  ·
    refine ⟨225343101295388037709178045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150228734196925358472785363 225343101295388037709178045)
    ·
      refine ⟨84503662985770514140941767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225343101295388037709178045 84503662985770514140941767)
      ·
        refine ⟨126755494478655771211412651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84503662985770514140941767 126755494478655771211412651)
        ·
          refine ⟨190133241717983656817118977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126755494478655771211412651 190133241717983656817118977)
          ·
            refine ⟨142599931288487742612839233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190133241717983656817118977 142599931288487742612839233)
            ·
              refine ⟨106949948466365806959629425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142599931288487742612839233 106949948466365806959629425)
              ·
                refine ⟨80212461349774355219722069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106949948466365806959629425 80212461349774355219722069)
                ·
                  refine ⟨469994890721334112615559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80212461349774355219722069 469994890721334112615559)
                  ·
                    rfl

theorem cell22_4118903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_4118903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118903 prefixEnd_4118903 := by exact prefixLift 4118903
  have htrace : WordTrace (prefixWord ++ tailWord_4118903) baseStart_4118903 baseEnd_4118903 := by
    simpa [prefixWord, tailWord_4118903, baseEnd_4118903] using wordTrace_append hprefix tailTrace_4118903
  have hstable : (prefixWord ++ tailWord_4118903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118903).length < 2 ^ (prefixWord ++ tailWord_4118903).sum := by decide
  have hdescent : baseEnd_4118903 < baseStart_4118903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118941 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_4118941 : Nat := 118140960795 + 4118941 * 2 ^ 59
def prefixEnd_4118941 : Nat := 4983230072969 + 3 ^ 40 * 4118941 * 2
def baseEnd_4118941 : Nat := 1409997680340582905396561

theorem tailTrace_4118941 : CollatzResearch.WordTrace tailWord_4118941 prefixEnd_4118941 1409997680340582905396561 := by
  unfold tailWord_4118941
  simp only [CollatzResearch.WordTrace]
  refine ⟨150230120170787690962668677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100153413447191793975112451 150230120170787690962668677)
  ·
    refine ⟨28168147532022692055500377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150230120170787690962668677 28168147532022692055500377)
    ·
      refine ⟨21126110649017019041625283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28168147532022692055500377 21126110649017019041625283)
      ·
        refine ⟨31689165973525528562437925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126110649017019041625283 31689165973525528562437925)
        ·
          refine ⟨5941718620036036605457111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31689165973525528562437925 5941718620036036605457111)
          ·
            refine ⟨8912577930054054908185667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941718620036036605457111 8912577930054054908185667)
            ·
              refine ⟨13368866895081082362278501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912577930054054908185667 13368866895081082362278501)
              ·
                refine ⟨2506662542827702942927219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13368866895081082362278501 2506662542827702942927219)
                ·
                  refine ⟨3759993814241554414390829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506662542827702942927219 3759993814241554414390829)
                  ·
                    refine ⟨1409997680340582905396561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759993814241554414390829 1409997680340582905396561)
                    ·
                      rfl

theorem cell22_4118941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_4118941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118941 prefixEnd_4118941 := by exact prefixLift 4118941
  have htrace : WordTrace (prefixWord ++ tailWord_4118941) baseStart_4118941 baseEnd_4118941 := by
    simpa [prefixWord, tailWord_4118941, baseEnd_4118941] using wordTrace_append hprefix tailTrace_4118941
  have hstable : (prefixWord ++ tailWord_4118941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118941).length < 2 ^ (prefixWord ++ tailWord_4118941).sum := by decide
  have hdescent : baseEnd_4118941 < baseStart_4118941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118952 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4118952 : Nat := 118140960795 + 4118952 * 2 ^ 59
def prefixEnd_4118952 : Nat := 4983230072969 + 3 ^ 40 * 4118952 * 2
def baseEnd_4118952 : Nat := 1410001445865382543371527

theorem tailTrace_4118952 : CollatzResearch.WordTrace tailWord_4118952 prefixEnd_4118952 1410001445865382543371527 := by
  unfold tailWord_4118952
  simp only [CollatzResearch.WordTrace]
  refine ⟨75115260686873919920659555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100153680915831893227546073 75115260686873919920659555)
  ·
    refine ⟨112672891030310879880989333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75115260686873919920659555 112672891030310879880989333)
    ·
      refine ⟨5281541767045822494421375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112672891030310879880989333 5281541767045822494421375)
      ·
        refine ⟨7922312650568733741632063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281541767045822494421375 7922312650568733741632063)
        ·
          refine ⟨11883468975853100612448095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922312650568733741632063 11883468975853100612448095)
          ·
            refine ⟨17825203463779650918672143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11883468975853100612448095 17825203463779650918672143)
            ·
              refine ⟨26737805195669476378008215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17825203463779650918672143 26737805195669476378008215)
              ·
                refine ⟨40106707793504214567012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26737805195669476378008215 40106707793504214567012323)
                ·
                  refine ⟨60160061690256321850518485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40106707793504214567012323 60160061690256321850518485)
                  ·
                    refine ⟨1410001445865382543371527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60160061690256321850518485 1410001445865382543371527)
                    ·
                      rfl

theorem cell22_4118952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4118952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118952 prefixEnd_4118952 := by exact prefixLift 4118952
  have htrace : WordTrace (prefixWord ++ tailWord_4118952) baseStart_4118952 baseEnd_4118952 := by
    simpa [prefixWord, tailWord_4118952, baseEnd_4118952] using wordTrace_append hprefix tailTrace_4118952
  have hstable : (prefixWord ++ tailWord_4118952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118952).length < 2 ^ (prefixWord ++ tailWord_4118952).sum := by decide
  have hdescent : baseEnd_4118952 < baseStart_4118952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118984 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_4118984 : Nat := 118140960795 + 4118984 * 2 ^ 59
def prefixEnd_4118984 : Nat := 4983230072969 + 3 ^ 40 * 4118984 * 2
def baseEnd_4118984 : Nat := 1410012400119345126571429

theorem tailTrace_4118984 : CollatzResearch.WordTrace tailWord_4118984 prefixEnd_4118984 1410012400119345126571429 := by
  unfold tailWord_4118984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75115844254815954653242003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100154459006421272870989337 75115844254815954653242003)
  ·
    refine ⟨112673766382223931979863005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75115844254815954653242003 112673766382223931979863005)
    ·
      refine ⟨42252662393333974492448627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112673766382223931979863005 42252662393333974492448627)
      ·
        refine ⟨63378993590000961738672941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42252662393333974492448627 63378993590000961738672941)
        ·
          refine ⟨23767122596250360652002353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63378993590000961738672941 23767122596250360652002353)
          ·
            refine ⟨17825341947187770489001765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23767122596250360652002353 17825341947187770489001765)
            ·
              refine ⟨3342251615097706966687831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17825341947187770489001765 3342251615097706966687831)
              ·
                refine ⟨5013377422646560450031747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342251615097706966687831 5013377422646560450031747)
                ·
                  refine ⟨7520066133969840675047621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013377422646560450031747 7520066133969840675047621)
                  ·
                    refine ⟨1410012400119345126571429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520066133969840675047621 1410012400119345126571429)
                    ·
                      rfl

theorem cell22_4118984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_4118984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4118984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4118984 prefixEnd_4118984 := by exact prefixLift 4118984
  have htrace : WordTrace (prefixWord ++ tailWord_4118984) baseStart_4118984 baseEnd_4118984 := by
    simpa [prefixWord, tailWord_4118984, baseEnd_4118984] using wordTrace_append hprefix tailTrace_4118984
  have hstable : (prefixWord ++ tailWord_4118984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118984).length < 2 ^ (prefixWord ++ tailWord_4118984).sum := by decide
  have hdescent : baseEnd_4118984 < baseStart_4118984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119025 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_4119025 : Nat := 118140960795 + 4119025 * 2 ^ 59
def prefixEnd_4119025 : Nat := 4983230072969 + 3 ^ 40 * 4119025 * 2
def baseEnd_4119025 : Nat := 1410026435257234686296303

theorem tailTrace_4119025 : CollatzResearch.WordTrace tailWord_4119025 prefixEnd_4119025 1410026435257234686296303 := by
  unfold tailWord_4119025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150233183902483373308726529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100155455934988915539151019 150233183902483373308726529)
  ·
    refine ⟨112674887926862529981544897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150233183902483373308726529 112674887926862529981544897)
    ·
      refine ⟨84506165945146897486158673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112674887926862529981544897 84506165945146897486158673)
      ·
        refine ⟨63379624458860173114619005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84506165945146897486158673 63379624458860173114619005)
        ·
          refine ⟨23767359172072564917982127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63379624458860173114619005 23767359172072564917982127)
          ·
            refine ⟨35651038758108847376973191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23767359172072564917982127 35651038758108847376973191)
            ·
              refine ⟨53476558137163271065459787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35651038758108847376973191 53476558137163271065459787)
              ·
                refine ⟨80214837205744906598189681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53476558137163271065459787 80214837205744906598189681)
                ·
                  refine ⟨60161127904308679948642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80214837205744906598189681 60161127904308679948642261)
                  ·
                    refine ⟨1410026435257234686296303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60161127904308679948642261 1410026435257234686296303)
                    ·
                      rfl

theorem cell22_4119025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_4119025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119025 prefixEnd_4119025 := by exact prefixLift 4119025
  have htrace : WordTrace (prefixWord ++ tailWord_4119025) baseStart_4119025 baseEnd_4119025 := by
    simpa [prefixWord, tailWord_4119025, baseEnd_4119025] using wordTrace_append hprefix tailTrace_4119025
  have hstable : (prefixWord ++ tailWord_4119025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119025).length < 2 ^ (prefixWord ++ tailWord_4119025).sum := by decide
  have hdescent : baseEnd_4119025 < baseStart_4119025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119110 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4119110 : Nat := 118140960795 + 4119110 * 2 ^ 59
def prefixEnd_4119110 : Nat := 4983230072969 + 3 ^ 40 * 4119110 * 2
def baseEnd_4119110 : Nat := 1410055532494322797921043

theorem tailTrace_4119110 : CollatzResearch.WordTrace tailWord_4119110 prefixEnd_4119110 1410055532494322797921043 := by
  unfold tailWord_4119110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694883878349232275799087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100157522738116955217047189 4694883878349232275799087)
  ·
    refine ⟨7042325817523848413698631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694883878349232275799087 7042325817523848413698631)
    ·
      refine ⟨10563488726285772620547947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042325817523848413698631 10563488726285772620547947)
      ·
        refine ⟨15845233089428658930821921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10563488726285772620547947 15845233089428658930821921)
        ·
          refine ⟨11883924817071494198116441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15845233089428658930821921 11883924817071494198116441)
          ·
            refine ⟨8912943612803620648587331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11883924817071494198116441 8912943612803620648587331)
            ·
              refine ⟨13369415419205430972880997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912943612803620648587331 13369415419205430972880997)
              ·
                refine ⟨2506765391101018307415187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13369415419205430972880997 2506765391101018307415187)
                ·
                  refine ⟨3760148086651527461122781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506765391101018307415187 3760148086651527461122781)
                  ·
                    refine ⟨1410055532494322797921043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3760148086651527461122781 1410055532494322797921043)
                    ·
                      rfl

theorem cell22_4119110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4119110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119110 prefixEnd_4119110 := by exact prefixLift 4119110
  have htrace : WordTrace (prefixWord ++ tailWord_4119110) baseStart_4119110 baseEnd_4119110 := by
    simpa [prefixWord, tailWord_4119110, baseEnd_4119110] using wordTrace_append hprefix tailTrace_4119110
  have hstable : (prefixWord ++ tailWord_4119110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119110).length < 2 ^ (prefixWord ++ tailWord_4119110).sum := by decide
  have hdescent : baseEnd_4119110 < baseStart_4119110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119147 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_4119147 : Nat := 118140960795 + 4119147 * 2 ^ 59
def prefixEnd_4119147 : Nat := 4983230072969 + 3 ^ 40 * 4119147 * 2
def baseEnd_4119147 : Nat := 1410068198350467034745929

theorem tailTrace_4119147 : CollatzResearch.WordTrace tailWord_4119147 prefixEnd_4119147 1410068198350467034745929 := by
  unfold tailWord_4119147
  simp only [CollatzResearch.WordTrace]
  refine ⟨150237633608041388144667695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100158422405360925429778463 150237633608041388144667695)
  ·
    refine ⟨225356450412062082217001543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150237633608041388144667695 225356450412062082217001543)
    ·
      refine ⟨338034675618093123325502315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225356450412062082217001543 338034675618093123325502315)
      ·
        refine ⟨507052013427139684988253473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338034675618093123325502315 507052013427139684988253473)
        ·
          refine ⟨380289010070354763741190105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507052013427139684988253473 380289010070354763741190105)
          ·
            refine ⟨285216757552766072805892579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380289010070354763741190105 285216757552766072805892579)
            ·
              refine ⟨427825136329149109208838869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285216757552766072805892579 427825136329149109208838869)
              ·
                refine ⟨10027151632714432247082161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427825136329149109208838869 10027151632714432247082161)
                ·
                  refine ⟨7520363724535824185311621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10027151632714432247082161 7520363724535824185311621)
                  ·
                    refine ⟨1410068198350467034745929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520363724535824185311621 1410068198350467034745929)
                    ·
                      rfl

theorem cell22_4119147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_4119147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119147 prefixEnd_4119147 := by exact prefixLift 4119147
  have htrace : WordTrace (prefixWord ++ tailWord_4119147) baseStart_4119147 baseEnd_4119147 := by
    simpa [prefixWord, tailWord_4119147, baseEnd_4119147] using wordTrace_append hprefix tailTrace_4119147
  have hstable : (prefixWord ++ tailWord_4119147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119147).length < 2 ^ (prefixWord ++ tailWord_4119147).sum := by decide
  have hdescent : baseEnd_4119147 < baseStart_4119147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119149 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4119149 : Nat := 118140960795 + 4119149 * 2 ^ 59
def prefixEnd_4119149 : Nat := 4983230072969 + 3 ^ 40 * 4119149 * 2
def baseEnd_4119149 : Nat := 1410068882991339696195923

theorem tailTrace_4119149 : CollatzResearch.WordTrace tailWord_4119149 prefixEnd_4119149 1410068882991339696195923 := by
  unfold tailWord_4119149
  simp only [CollatzResearch.WordTrace]
  refine ⟨150237706554034142486240501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100158471036022761657493667 150237706554034142486240501)
  ·
    refine ⟨14084784989440700858085047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150237706554034142486240501 14084784989440700858085047)
    ·
      refine ⟨21127177484161051287127571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14084784989440700858085047 21127177484161051287127571)
      ·
        refine ⟨31690766226241576930691357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21127177484161051287127571 31690766226241576930691357)
        ·
          refine ⟨11884037334840591349009259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31690766226241576930691357 11884037334840591349009259)
          ·
            refine ⟨17826056002260887023513889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884037334840591349009259 17826056002260887023513889)
            ·
              refine ⟨13369542001695665267635417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17826056002260887023513889 13369542001695665267635417)
              ·
                refine ⟨10027156501271748950726563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13369542001695665267635417 10027156501271748950726563)
                ·
                  refine ⟨15040734751907623426089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10027156501271748950726563 15040734751907623426089845)
                  ·
                    refine ⟨1410068882991339696195923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15040734751907623426089845 1410068882991339696195923)
                    ·
                      rfl

theorem cell22_4119149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4119149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119149 prefixEnd_4119149 := by exact prefixLift 4119149
  have htrace : WordTrace (prefixWord ++ tailWord_4119149) baseStart_4119149 baseEnd_4119149 := by
    simpa [prefixWord, tailWord_4119149, baseEnd_4119149] using wordTrace_append hprefix tailTrace_4119149
  have hstable : (prefixWord ++ tailWord_4119149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119149).length < 2 ^ (prefixWord ++ tailWord_4119149).sum := by decide
  have hdescent : baseEnd_4119149 < baseStart_4119149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119196 : List Nat := [2, 2, 3, 2, 2, 3, 2, 6]
def baseStart_4119196 : Nat := 118140960795 + 4119196 * 2 ^ 59
def prefixEnd_4119196 : Nat := 4983230072969 + 3 ^ 40 * 4119196 * 2
def baseEnd_4119196 : Nat := 156676108005760804474531

theorem tailTrace_4119196 : CollatzResearch.WordTrace tailWord_4119196 prefixEnd_4119196 156676108005760804474531 := by
  unfold tailWord_4119196
  simp only [CollatzResearch.WordTrace]
  refine ⟨75119710392431934756600721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100159613856575913008800961 75119710392431934756600721)
  ·
    refine ⟨56339782794323951067450541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75119710392431934756600721 56339782794323951067450541)
    ·
      refine ⟨21127418547871481650293953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56339782794323951067450541 21127418547871481650293953)
      ·
        refine ⟨15845563910903611237720465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21127418547871481650293953 15845563910903611237720465)
        ·
          refine ⟨11884172933177708428290349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15845563910903611237720465 11884172933177708428290349)
          ·
            refine ⟨4456564849941640660608881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11884172933177708428290349 4456564849941640660608881)
            ·
              refine ⟨3342423637456230495456661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456564849941640660608881 3342423637456230495456661)
              ·
                refine ⟨156676108005760804474531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3342423637456230495456661 156676108005760804474531)
                ·
                  rfl

theorem cell22_4119196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_4119196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119196 prefixEnd_4119196 := by exact prefixLift 4119196
  have htrace : WordTrace (prefixWord ++ tailWord_4119196) baseStart_4119196 baseEnd_4119196 := by
    simpa [prefixWord, tailWord_4119196, baseEnd_4119196] using wordTrace_append hprefix tailTrace_4119196
  have hstable : (prefixWord ++ tailWord_4119196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119196).length < 2 ^ (prefixWord ++ tailWord_4119196).sum := by decide
  have hdescent : baseEnd_4119196 < baseStart_4119196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119374 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_4119374 : Nat := 118140960795 + 4119374 * 2 ^ 59
def prefixEnd_4119374 : Nat := 4983230072969 + 3 ^ 40 * 4119374 * 2
def baseEnd_4119374 : Nat := 1410145905089514109320233

theorem tailTrace_4119374 : CollatzResearch.WordTrace tailWord_4119374 prefixEnd_4119374 1410145905089514109320233 := by
  unfold tailWord_4119374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18780739122277375739147647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100163941985479337275454117 18780739122277375739147647)
  ·
    refine ⟨28171108683416063608721471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18780739122277375739147647 28171108683416063608721471)
    ·
      refine ⟨42256663025124095413082207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28171108683416063608721471 42256663025124095413082207)
      ·
        refine ⟨63384994537686143119623311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42256663025124095413082207 63384994537686143119623311)
        ·
          refine ⟨95077491806529214679434967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63384994537686143119623311 95077491806529214679434967)
          ·
            refine ⟨142616237709793822019152451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95077491806529214679434967 142616237709793822019152451)
            ·
              refine ⟨213924356564690733028728677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142616237709793822019152451 213924356564690733028728677)
              ·
                refine ⟨40110816855879512442886627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213924356564690733028728677 40110816855879512442886627)
                ·
                  refine ⟨60166225283819268664329941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40110816855879512442886627 60166225283819268664329941)
                  ·
                    refine ⟨1410145905089514109320233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60166225283819268664329941 1410145905089514109320233)
                    ·
                      rfl

theorem cell22_4119374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_4119374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119374 prefixEnd_4119374 := by exact prefixLift 4119374
  have htrace : WordTrace (prefixWord ++ tailWord_4119374) baseStart_4119374 baseEnd_4119374 := by
    simpa [prefixWord, tailWord_4119374, baseEnd_4119374] using wordTrace_append hprefix tailTrace_4119374
  have hstable : (prefixWord ++ tailWord_4119374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119374).length < 2 ^ (prefixWord ++ tailWord_4119374).sum := by decide
  have hdescent : baseEnd_4119374 < baseStart_4119374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119436 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_4119436 : Nat := 118140960795 + 4119436 * 2 ^ 59
def prefixEnd_4119436 : Nat := 4983230072969 + 3 ^ 40 * 4119436 * 2
def baseEnd_4119436 : Nat := 1410167128956566614270043

theorem tailTrace_4119436 : CollatzResearch.WordTrace tailWord_4119436 prefixEnd_4119436 1410167128956566614270043 := by
  unfold tailWord_4119436
  simp only [CollatzResearch.WordTrace]
  refine ⟨75124087151997195250969081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100165449535996260334625441 75124087151997195250969081)
  ·
    refine ⟨56343065363997896438226811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75124087151997195250969081 56343065363997896438226811)
    ·
      refine ⟨84514598045996844657340217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56343065363997896438226811 84514598045996844657340217)
      ·
        refine ⟨63385948534497633493005163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84514598045996844657340217 63385948534497633493005163)
        ·
          refine ⟨95078922801746450239507745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63385948534497633493005163 95078922801746450239507745)
          ·
            refine ⟨71309192101309837679630809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95078922801746450239507745 71309192101309837679630809)
            ·
              refine ⟨53481894075982378259723107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71309192101309837679630809 53481894075982378259723107)
              ·
                refine ⟨80222841113973567389584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53481894075982378259723107 80222841113973567389584661)
                ·
                  refine ⟨3760445677217510971386781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80222841113973567389584661 3760445677217510971386781)
                  ·
                    refine ⟨1410167128956566614270043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3760445677217510971386781 1410167128956566614270043)
                    ·
                      rfl

theorem cell22_4119436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_4119436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119436 prefixEnd_4119436 := by exact prefixLift 4119436
  have htrace : WordTrace (prefixWord ++ tailWord_4119436) baseStart_4119436 baseEnd_4119436 := by
    simpa [prefixWord, tailWord_4119436, baseEnd_4119436] using wordTrace_append hprefix tailTrace_4119436
  have hstable : (prefixWord ++ tailWord_4119436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119436).length < 2 ^ (prefixWord ++ tailWord_4119436).sum := by decide
  have hdescent : baseEnd_4119436 < baseStart_4119436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119455 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 4]
def baseStart_4119455 : Nat := 118140960795 + 4119455 * 2 ^ 59
def prefixEnd_4119455 : Nat := 4983230072969 + 3 ^ 40 * 4119455 * 2
def baseEnd_4119455 : Nat := 470057877681618966014995

theorem tailTrace_4119455 : CollatzResearch.WordTrace tailWord_4119455 prefixEnd_4119455 470057877681618966014995 := by
  unfold tailWord_4119455
  simp only [CollatzResearch.WordTrace]
  refine ⟨150248867290925556746879819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100165911527283704497919879 150248867290925556746879819)
  ·
    refine ⟨225373300936388335120319729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150248867290925556746879819 225373300936388335120319729)
    ·
      refine ⟨169029975702291251340239797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225373300936388335120319729 169029975702291251340239797)
      ·
        refine ⟨15846560222089804813147481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169029975702291251340239797 15846560222089804813147481)
        ·
          refine ⟨11884920166567353609860611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15846560222089804813147481 11884920166567353609860611)
          ·
            refine ⟨17827380249851030414790917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884920166567353609860611 17827380249851030414790917)
            ·
              refine ⟨3342633796847068202773297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17827380249851030414790917 3342633796847068202773297)
              ·
                refine ⟨2506975347635301152079973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342633796847068202773297 2506975347635301152079973)
                ·
                  refine ⟨470057877681618966014995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2506975347635301152079973 470057877681618966014995)
                  ·
                    rfl

theorem cell22_4119455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 4].length) (baseStart_4119455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119455 prefixEnd_4119455 := by exact prefixLift 4119455
  have htrace : WordTrace (prefixWord ++ tailWord_4119455) baseStart_4119455 baseEnd_4119455 := by
    simpa [prefixWord, tailWord_4119455, baseEnd_4119455] using wordTrace_append hprefix tailTrace_4119455
  have hstable : (prefixWord ++ tailWord_4119455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119455).length < 2 ^ (prefixWord ++ tailWord_4119455).sum := by decide
  have hdescent : baseEnd_4119455 < baseStart_4119455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119485 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_4119485 : Nat := 118140960795 + 4119485 * 2 ^ 59
def prefixEnd_4119485 : Nat := 4983230072969 + 3 ^ 40 * 4119485 * 2
def baseEnd_4119485 : Nat := 1410183902657946819794893

theorem tailTrace_4119485 : CollatzResearch.WordTrace tailWord_4119485 prefixEnd_4119485 1410183902657946819794893 := by
  unfold tailWord_4119485
  simp only [CollatzResearch.WordTrace]
  refine ⟨150249961480816871870471909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100166640987211247913647939 150249961480816871870471909)
  ·
    refine ⟨28171867777653163475713483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150249961480816871870471909 28171867777653163475713483)
    ·
      refine ⟨42257801666479745213570225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28171867777653163475713483 42257801666479745213570225)
      ·
        refine ⟨31693351249859808910177669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42257801666479745213570225 31693351249859808910177669)
        ·
          refine ⟨5942503359348714170658313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31693351249859808910177669 5942503359348714170658313)
          ·
            refine ⟨4456877519511535627993735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5942503359348714170658313 4456877519511535627993735)
            ·
              refine ⟨6685316279267303441990603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456877519511535627993735 6685316279267303441990603)
              ·
                refine ⟨10027974418900955162985905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685316279267303441990603 10027974418900955162985905)
                ·
                  refine ⟨7520980814175716372239429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10027974418900955162985905 7520980814175716372239429)
                  ·
                    refine ⟨1410183902657946819794893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520980814175716372239429 1410183902657946819794893)
                    ·
                      rfl

theorem cell22_4119485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_4119485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119485 prefixEnd_4119485 := by exact prefixLift 4119485
  have htrace : WordTrace (prefixWord ++ tailWord_4119485) baseStart_4119485 baseEnd_4119485 := by
    simpa [prefixWord, tailWord_4119485, baseEnd_4119485] using wordTrace_append hprefix tailTrace_4119485
  have hstable : (prefixWord ++ tailWord_4119485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119485).length < 2 ^ (prefixWord ++ tailWord_4119485).sum := by decide
  have hdescent : baseEnd_4119485 < baseStart_4119485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119511 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 5]
def baseStart_4119511 : Nat := 118140960795 + 4119511 * 2 ^ 59
def prefixEnd_4119511 : Nat := 4983230072969 + 3 ^ 40 * 4119511 * 2
def baseEnd_4119511 : Nat := 470064267663097139548271

theorem tailTrace_4119511 : CollatzResearch.WordTrace tailWord_4119511 prefixEnd_4119511 470064267663097139548271 := by
  unfold tailWord_4119511
  simp only [CollatzResearch.WordTrace]
  refine ⟨150250909778722678310918387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100167273185815118873945591 150250909778722678310918387)
  ·
    refine ⟨225376364668084017466377581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150250909778722678310918387 225376364668084017466377581)
    ·
      refine ⟨84516136750531506549891593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225376364668084017466377581 84516136750531506549891593)
      ·
        refine ⟨63387102562898629912418695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84516136750531506549891593 63387102562898629912418695)
        ·
          refine ⟨95080653844347944868628043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63387102562898629912418695 95080653844347944868628043)
          ·
            refine ⟨142620980766521917302942065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95080653844347944868628043 142620980766521917302942065)
            ·
              refine ⟨106965735574891437977206549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142620980766521917302942065 106965735574891437977206549)
              ·
                refine ⟨5014018855073036155181557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106965735574891437977206549 5014018855073036155181557)
                ·
                  refine ⟨470064267663097139548271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014018855073036155181557 470064267663097139548271)
                  ·
                    rfl

theorem cell22_4119511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].length) (baseStart_4119511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119511 prefixEnd_4119511 := by exact prefixLift 4119511
  have htrace : WordTrace (prefixWord ++ tailWord_4119511) baseStart_4119511 baseEnd_4119511 := by
    simpa [prefixWord, tailWord_4119511, baseEnd_4119511] using wordTrace_append hprefix tailTrace_4119511
  have hstable : (prefixWord ++ tailWord_4119511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119511).length < 2 ^ (prefixWord ++ tailWord_4119511).sum := by decide
  have hdescent : baseEnd_4119511 < baseStart_4119511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119573 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 6]
def baseStart_4119573 : Nat := 118140960795 + 4119573 * 2 ^ 59
def prefixEnd_4119573 : Nat := 4983230072969 + 3 ^ 40 * 4119573 * 2
def baseEnd_4119573 : Nat := 470071342285447974531541

theorem tailTrace_4119573 : CollatzResearch.WordTrace tailWord_4119573 prefixEnd_4119573 470071342285447974531541 := by
  unfold tailWord_4119573
  simp only [CollatzResearch.WordTrace]
  refine ⟨150253171104498062899675373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100168780736332041933116915 150253171104498062899675373)
  ·
    refine ⟨56344939164186773587378265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150253171104498062899675373 56344939164186773587378265)
    ·
      refine ⟨42258704373140080190533699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56344939164186773587378265 42258704373140080190533699)
      ·
        refine ⟨63388056559710120285800549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42258704373140080190533699 63388056559710120285800549)
        ·
          refine ⟨11885260604945647553587603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63388056559710120285800549 11885260604945647553587603)
          ·
            refine ⟨17827890907418471330381405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11885260604945647553587603 17827890907418471330381405)
            ·
              refine ⟨6685459090281926748893027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17827890907418471330381405 6685459090281926748893027)
              ·
                refine ⟨10028188635422890123339541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685459090281926748893027 10028188635422890123339541)
                ·
                  refine ⟨470071342285447974531541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10028188635422890123339541 470071342285447974531541)
                  ·
                    rfl

theorem cell22_4119573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_4119573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119573 prefixEnd_4119573 := by exact prefixLift 4119573
  have htrace : WordTrace (prefixWord ++ tailWord_4119573) baseStart_4119573 baseEnd_4119573 := by
    simpa [prefixWord, tailWord_4119573, baseEnd_4119573] using wordTrace_append hprefix tailTrace_4119573
  have hstable : (prefixWord ++ tailWord_4119573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119573).length < 2 ^ (prefixWord ++ tailWord_4119573).sum := by decide
  have hdescent : baseEnd_4119573 < baseStart_4119573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119601 : List Nat := [1, 2, 2, 3, 1, 2, 1, 10]
def baseStart_4119601 : Nat := 118140960795 + 4119601 * 2 ^ 59
def prefixEnd_4119601 : Nat := 4983230072969 + 3 ^ 40 * 4119601 * 2
def baseEnd_4119601 : Nat := 156691512425395687099393

theorem tailTrace_4119601 : CollatzResearch.WordTrace tailWord_4119601 prefixEnd_4119601 156691512425395687099393 := by
  unfold tailWord_4119601
  simp only [CollatzResearch.WordTrace]
  refine ⟨150254192348396623681694657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100169461565597749121129771 150254192348396623681694657)
  ·
    refine ⟨112690644261297467761270993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150254192348396623681694657 112690644261297467761270993)
    ·
      refine ⟨84517983195973100820953245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112690644261297467761270993 84517983195973100820953245)
      ·
        refine ⟨31694243698489912807857467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84517983195973100820953245 31694243698489912807857467)
        ·
          refine ⟨47541365547734869211786201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31694243698489912807857467 47541365547734869211786201)
          ·
            refine ⟨35656024160801151908839651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47541365547734869211786201 35656024160801151908839651)
            ·
              refine ⟨53484036241201727863259477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35656024160801151908839651 53484036241201727863259477)
              ·
                refine ⟨156691512425395687099393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53484036241201727863259477 156691512425395687099393)
                ·
                  rfl

theorem cell22_4119601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 10].length) (baseStart_4119601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119601 prefixEnd_4119601 := by exact prefixLift 4119601
  have htrace : WordTrace (prefixWord ++ tailWord_4119601) baseStart_4119601 baseEnd_4119601 := by
    simpa [prefixWord, tailWord_4119601, baseEnd_4119601] using wordTrace_append hprefix tailTrace_4119601
  have hstable : (prefixWord ++ tailWord_4119601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119601).length < 2 ^ (prefixWord ++ tailWord_4119601).sum := by decide
  have hdescent : baseEnd_4119601 < baseStart_4119601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119742 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_4119742 : Nat := 118140960795 + 4119742 * 2 ^ 59
def prefixEnd_4119742 : Nat := 4983230072969 + 3 ^ 40 * 4119742 * 2
def baseEnd_4119742 : Nat := 470090626336694605373035

theorem tailTrace_4119742 : CollatzResearch.WordTrace tailWord_4119742 prefixEnd_4119742 470090626336694605373035 := by
  unfold tailWord_4119742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18782416880110725595322185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100172890027257203175051653 18782416880110725595322185)
  ·
    refine ⟨14086812660083044196491639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18782416880110725595322185 14086812660083044196491639)
    ·
      refine ⟨21130218990124566294737459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14086812660083044196491639 21130218990124566294737459)
      ·
        refine ⟨31695328485186849442106189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21130218990124566294737459 31695328485186849442106189)
        ·
          refine ⟨11885748181945068540789821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31695328485186849442106189 11885748181945068540789821)
          ·
            refine ⟨4457155568229400702796183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11885748181945068540789821 4457155568229400702796183)
            ·
              refine ⟨6685733352344101054194275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457155568229400702796183 6685733352344101054194275)
              ·
                refine ⟨10028600028516151581291413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685733352344101054194275 10028600028516151581291413)
                ·
                  refine ⟨470090626336694605373035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10028600028516151581291413 470090626336694605373035)
                  ·
                    rfl

theorem cell22_4119742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_4119742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119742 prefixEnd_4119742 := by exact prefixLift 4119742
  have htrace : WordTrace (prefixWord ++ tailWord_4119742) baseStart_4119742 baseEnd_4119742 := by
    simpa [prefixWord, tailWord_4119742, baseEnd_4119742] using wordTrace_append hprefix tailTrace_4119742
  have hstable : (prefixWord ++ tailWord_4119742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119742).length < 2 ^ (prefixWord ++ tailWord_4119742).sum := by decide
  have hdescent : baseEnd_4119742 < baseStart_4119742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119892 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_4119892 : Nat := 118140960795 + 4119892 * 2 ^ 59
def prefixEnd_4119892 : Nat := 4983230072969 + 3 ^ 40 * 4119892 * 2
def baseEnd_4119892 : Nat := 1410323227075533424868645

theorem tailTrace_4119892 : CollatzResearch.WordTrace tailWord_4119892 prefixEnd_4119892 1410323227075533424868645 := by
  unfold tailWord_4119892
  simp only [CollatzResearch.WordTrace]
  refine ⟨75132402995171190190268965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100176537326894920253691953 75132402995171190190268965)
  ·
    refine ⟨14087325561594598160675431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75132402995171190190268965 14087325561594598160675431)
    ·
      refine ⟨21130988342391897241013147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087325561594598160675431 21130988342391897241013147)
      ·
        refine ⟨31696482513587845861519721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21130988342391897241013147 31696482513587845861519721)
        ·
          refine ⟨23772361885190884396139791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31696482513587845861519721 23772361885190884396139791)
          ·
            refine ⟨35658542827786326594209687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772361885190884396139791 35658542827786326594209687)
            ·
              refine ⟨53487814241679489891314531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35658542827786326594209687 53487814241679489891314531)
              ·
                refine ⟨80231721362519234836971797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53487814241679489891314531 80231721362519234836971797)
                ·
                  refine ⟨3760861938868089132983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80231721362519234836971797 3760861938868089132983053)
                  ·
                    refine ⟨1410323227075533424868645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3760861938868089132983053 1410323227075533424868645)
                    ·
                      rfl

theorem cell22_4119892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_4119892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119892 prefixEnd_4119892 := by exact prefixLift 4119892
  have htrace : WordTrace (prefixWord ++ tailWord_4119892) baseStart_4119892 baseEnd_4119892 := by
    simpa [prefixWord, tailWord_4119892, baseEnd_4119892] using wordTrace_append hprefix tailTrace_4119892
  have hstable : (prefixWord ++ tailWord_4119892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119892).length < 2 ^ (prefixWord ++ tailWord_4119892).sum := by decide
  have hdescent : baseEnd_4119892 < baseStart_4119892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119907 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_4119907 : Nat := 118140960795 + 4119907 * 2 ^ 59
def prefixEnd_4119907 : Nat := 4983230072969 + 3 ^ 40 * 4119907 * 2
def baseEnd_4119907 : Nat := 1410328361882078385743599

theorem tailTrace_4119907 : CollatzResearch.WordTrace tailWord_4119907 prefixEnd_4119907 1410328361882078385743599 := by
  unfold tailWord_4119907
  simp only [CollatzResearch.WordTrace]
  refine ⟨150265353085288037942333975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100176902056858691961555983 150265353085288037942333975)
  ·
    refine ⟨225398029627932056913500963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150265353085288037942333975 225398029627932056913500963)
    ·
      refine ⟨338097044441898085370251445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225398029627932056913500963 338097044441898085370251445)
      ·
        refine ⟨31696597916427945503461073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338097044441898085370251445 31696597916427945503461073)
        ·
          refine ⟨23772448437320959127595805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31696597916427945503461073 23772448437320959127595805)
          ·
            refine ⟨8914668163995359672848427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23772448437320959127595805 8914668163995359672848427)
            ·
              refine ⟨13372002245993039509272641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914668163995359672848427 13372002245993039509272641)
              ·
                refine ⟨10029001684494779631954481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372002245993039509272641 10029001684494779631954481)
                ·
                  refine ⟨7521751263371084723965861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029001684494779631954481 7521751263371084723965861)
                  ·
                    refine ⟨1410328361882078385743599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521751263371084723965861 1410328361882078385743599)
                    ·
                      rfl

theorem cell22_4119907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_4119907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119907 prefixEnd_4119907 := by exact prefixLift 4119907
  have htrace : WordTrace (prefixWord ++ tailWord_4119907) baseStart_4119907 baseEnd_4119907 := by
    simpa [prefixWord, tailWord_4119907, baseEnd_4119907] using wordTrace_append hprefix tailTrace_4119907
  have hstable : (prefixWord ++ tailWord_4119907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119907).length < 2 ^ (prefixWord ++ tailWord_4119907).sum := by decide
  have hdescent : baseEnd_4119907 < baseStart_4119907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119911 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 4]
def baseStart_4119911 : Nat := 118140960795 + 4119911 * 2 ^ 59
def prefixEnd_4119911 : Nat := 4983230072969 + 3 ^ 40 * 4119911 * 2
def baseEnd_4119911 : Nat := 470109910387941236214529

theorem tailTrace_4119911 : CollatzResearch.WordTrace tailWord_4119911 prefixEnd_4119911 470109910387941236214529 := by
  unfold tailWord_4119911
  simp only [CollatzResearch.WordTrace]
  refine ⟨150265498977273546625479587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100176999318182364416986391 150265498977273546625479587)
  ·
    refine ⟨225398248465910319938219381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150265498977273546625479587 225398248465910319938219381)
    ·
      refine ⟨21131085793679092494208067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225398248465910319938219381 21131085793679092494208067)
      ·
        refine ⟨31696628690518638741312101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21131085793679092494208067 31696628690518638741312101)
        ·
          refine ⟨5943117879472244763996019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31696628690518638741312101 5943117879472244763996019)
          ·
            refine ⟨8914676819208367145994029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943117879472244763996019 8914676819208367145994029)
            ·
              refine ⟨3343003807203137679747761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8914676819208367145994029 3343003807203137679747761)
              ·
                refine ⟨2507252855402353259810821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343003807203137679747761 2507252855402353259810821)
                ·
                  refine ⟨470109910387941236214529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507252855402353259810821 470109910387941236214529)
                  ·
                    rfl

theorem cell22_4119911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 4].length) (baseStart_4119911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119911 prefixEnd_4119911 := by exact prefixLift 4119911
  have htrace : WordTrace (prefixWord ++ tailWord_4119911) baseStart_4119911 baseEnd_4119911 := by
    simpa [prefixWord, tailWord_4119911, baseEnd_4119911] using wordTrace_append hprefix tailTrace_4119911
  have hstable : (prefixWord ++ tailWord_4119911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119911).length < 2 ^ (prefixWord ++ tailWord_4119911).sum := by decide
  have hdescent : baseEnd_4119911 < baseStart_4119911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119967 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 5]
def baseStart_4119967 : Nat := 118140960795 + 4119967 * 2 ^ 59
def prefixEnd_4119967 : Nat := 4983230072969 + 3 ^ 40 * 4119967 * 2
def baseEnd_4119967 : Nat := 470116300369419409747805

theorem tailTrace_4119967 : CollatzResearch.WordTrace tailWord_4119967 prefixEnd_4119967 470116300369419409747805 := by
  unfold tailWord_4119967
  simp only [CollatzResearch.WordTrace]
  refine ⟨150267541465070668189518155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100178360976713778793012103 150267541465070668189518155)
  ·
    refine ⟨225401312197606002284277233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150267541465070668189518155 225401312197606002284277233)
    ·
      refine ⟨169050984148204501713207925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225401312197606002284277233 169050984148204501713207925)
      ·
        refine ⟨15848529763894172035613243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169050984148204501713207925 15848529763894172035613243)
        ·
          refine ⟨23772794645841258053419865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15848529763894172035613243 23772794645841258053419865)
          ·
            refine ⟨17829595984380943540064899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23772794645841258053419865 17829595984380943540064899)
            ·
              refine ⟨26744393976571415310097349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829595984380943540064899 26744393976571415310097349)
              ·
                refine ⟨5014573870607140370643253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26744393976571415310097349 5014573870607140370643253)
                ·
                  refine ⟨470116300369419409747805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014573870607140370643253 470116300369419409747805)
                  ·
                    rfl

theorem cell22_4119967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].length) (baseStart_4119967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119967 prefixEnd_4119967 := by exact prefixLift 4119967
  have htrace : WordTrace (prefixWord ++ tailWord_4119967) baseStart_4119967 baseEnd_4119967 := by
    simpa [prefixWord, tailWord_4119967, baseEnd_4119967] using wordTrace_append hprefix tailTrace_4119967
  have hstable : (prefixWord ++ tailWord_4119967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119967).length < 2 ^ (prefixWord ++ tailWord_4119967).sum := by decide
  have hdescent : baseEnd_4119967 < baseStart_4119967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119997 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4119997 : Nat := 118140960795 + 4119997 * 2 ^ 59
def prefixEnd_4119997 : Nat := 4983230072969 + 3 ^ 40 * 4119997 * 2
def baseEnd_4119997 : Nat := 1410359170721348150993323

theorem tailTrace_4119997 : CollatzResearch.WordTrace tailWord_4119997 prefixEnd_4119997 1410359170721348150993323 := by
  unfold tailWord_4119997
  simp only [CollatzResearch.WordTrace]
  refine ⟨150268635654961983313110245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100179090436641322208740163 150268635654961983313110245)
  ·
    refine ⟨28175369185305371871208171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150268635654961983313110245 28175369185305371871208171)
    ·
      refine ⟨42263053777958057806812257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28175369185305371871208171 42263053777958057806812257)
      ·
        refine ⟨31697290333468543355109193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42263053777958057806812257 31697290333468543355109193)
        ·
          refine ⟨23772967750101407516331895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31697290333468543355109193 23772967750101407516331895)
          ·
            refine ⟨35659451625152111274497843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772967750101407516331895 35659451625152111274497843)
            ·
              refine ⟨53489177437728166911746765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35659451625152111274497843 53489177437728166911746765)
              ·
                refine ⟨20058441539148062591905037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53489177437728166911746765 20058441539148062591905037)
                ·
                  refine ⟨7521915577180523471964389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20058441539148062591905037 7521915577180523471964389)
                  ·
                    refine ⟨1410359170721348150993323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521915577180523471964389 1410359170721348150993323)
                    ·
                      rfl

theorem cell22_4119997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4119997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4119997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4119997 prefixEnd_4119997 := by exact prefixLift 4119997
  have htrace : WordTrace (prefixWord ++ tailWord_4119997) baseStart_4119997 baseEnd_4119997 := by
    simpa [prefixWord, tailWord_4119997, baseEnd_4119997] using wordTrace_append hprefix tailTrace_4119997
  have hstable : (prefixWord ++ tailWord_4119997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119997).length < 2 ^ (prefixWord ++ tailWord_4119997).sum := by decide
  have hdescent : baseEnd_4119997 < baseStart_4119997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120029 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4120029 : Nat := 118140960795 + 4120029 * 2 ^ 59
def prefixEnd_4120029 : Nat := 4983230072969 + 3 ^ 40 * 4120029 * 2
def baseEnd_4120029 : Nat := 470123374991770244731075

theorem tailTrace_4120029 : CollatzResearch.WordTrace tailWord_4120029 prefixEnd_4120029 470123374991770244731075 := by
  unfold tailWord_4120029
  simp only [CollatzResearch.WordTrace]
  refine ⟨150269802790846052778275141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100179868527230701852183427 150269802790846052778275141)
  ·
    refine ⟨28175588023283634895926589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150269802790846052778275141 28175588023283634895926589)
    ·
      refine ⟨10565845508731363085972471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28175588023283634895926589 10565845508731363085972471)
      ·
        refine ⟨15848768263097044628958707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10565845508731363085972471 15848768263097044628958707)
        ·
          refine ⟨23773152394645566943438061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15848768263097044628958707 23773152394645566943438061)
          ·
            refine ⟨8914932147992087603789273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23773152394645566943438061 8914932147992087603789273)
            ·
              refine ⟨6686199110994065702841955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8914932147992087603789273 6686199110994065702841955)
              ·
                refine ⟨10029298666491098554262933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686199110994065702841955 10029298666491098554262933)
                ·
                  refine ⟨470123374991770244731075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10029298666491098554262933 470123374991770244731075)
                  ·
                    rfl

theorem cell22_4120029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4120029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120029 prefixEnd_4120029 := by exact prefixLift 4120029
  have htrace : WordTrace (prefixWord ++ tailWord_4120029) baseStart_4120029 baseEnd_4120029 := by
    simpa [prefixWord, tailWord_4120029, baseEnd_4120029] using wordTrace_append hprefix tailTrace_4120029
  have hstable : (prefixWord ++ tailWord_4120029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120029).length < 2 ^ (prefixWord ++ tailWord_4120029).sum := by decide
  have hdescent : baseEnd_4120029 < baseStart_4120029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120140 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_4120140 : Nat := 118140960795 + 4120140 * 2 ^ 59
def prefixEnd_4120140 : Nat := 4983230072969 + 3 ^ 40 * 4120140 * 2
def baseEnd_4120140 : Nat := 1410408122543743444667885

theorem tailTrace_4120140 : CollatzResearch.WordTrace tailWord_4120140 prefixEnd_4120140 1410408122543743444667885 := by
  unfold tailWord_4120140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75136925646721959367782937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100182567528962612490377249 75136925646721959367782937)
  ·
    refine ⟨56352694235041469525837203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75136925646721959367782937 56352694235041469525837203)
    ·
      refine ⟨84529041352562204288755805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56352694235041469525837203 84529041352562204288755805)
      ·
        refine ⟨31698390507210826608283427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84529041352562204288755805 31698390507210826608283427)
        ·
          refine ⟨47547585760816239912425141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31698390507210826608283427 47547585760816239912425141)
          ·
            refine ⟨4457586165076522491789857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47547585760816239912425141 4457586165076522491789857)
            ·
              refine ⟨3343189623807391868842393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457586165076522491789857 3343189623807391868842393)
              ·
                refine ⟨2507392217855543901631795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343189623807391868842393 2507392217855543901631795)
                ·
                  refine ⟨3761088326783315852447693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507392217855543901631795 3761088326783315852447693)
                  ·
                    refine ⟨1410408122543743444667885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761088326783315852447693 1410408122543743444667885)
                    ·
                      rfl

theorem cell22_4120140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_4120140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120140 prefixEnd_4120140 := by exact prefixLift 4120140
  have htrace : WordTrace (prefixWord ++ tailWord_4120140) baseStart_4120140 baseEnd_4120140 := by
    simpa [prefixWord, tailWord_4120140, baseEnd_4120140] using wordTrace_append hprefix tailTrace_4120140
  have hstable : (prefixWord ++ tailWord_4120140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120140).length < 2 ^ (prefixWord ++ tailWord_4120140).sum := by decide
  have hdescent : baseEnd_4120140 < baseStart_4120140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120164 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_4120164 : Nat := 118140960795 + 4120164 * 2 ^ 59
def prefixEnd_4120164 : Nat := 4983230072969 + 3 ^ 40 * 4120164 * 2
def baseEnd_4120164 : Nat := 470138779411405127355937

theorem tailTrace_4120164 : CollatzResearch.WordTrace tailWord_4120164 prefixEnd_4120164 470138779411405127355937 := by
  unfold tailWord_4120164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75137363322678485417219773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100183151096904647222959697 75137363322678485417219773)
  ·
    refine ⟨28176511246004432031457415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75137363322678485417219773 28176511246004432031457415)
    ·
      refine ⟨42264766869006648047186123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28176511246004432031457415 42264766869006648047186123)
      ·
        refine ⟨63397150303509972070779185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42264766869006648047186123 63397150303509972070779185)
        ·
          refine ⟨47547862727632479053084389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63397150303509972070779185 47547862727632479053084389)
          ·
            refine ⟨8915224261431089822453323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47547862727632479053084389 8915224261431089822453323)
            ·
              refine ⟨13372836392146634733679985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915224261431089822453323 13372836392146634733679985)
              ·
                refine ⟨10029627294109976050259989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372836392146634733679985 10029627294109976050259989)
                ·
                  refine ⟨470138779411405127355937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10029627294109976050259989 470138779411405127355937)
                  ·
                    rfl

theorem cell22_4120164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_4120164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120164 prefixEnd_4120164 := by exact prefixLift 4120164
  have htrace : WordTrace (prefixWord ++ tailWord_4120164) baseStart_4120164 baseEnd_4120164 := by
    simpa [prefixWord, tailWord_4120164, baseEnd_4120164] using wordTrace_append hprefix tailTrace_4120164
  have hstable : (prefixWord ++ tailWord_4120164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120164).length < 2 ^ (prefixWord ++ tailWord_4120164).sum := by decide
  have hdescent : baseEnd_4120164 < baseStart_4120164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120192 : List Nat := [2, 1, 1, 2, 1, 4, 11]
def baseStart_4120192 : Nat := 118140960795 + 4120192 * 2 ^ 59
def prefixEnd_4120192 : Nat := 4983230072969 + 3 ^ 40 * 4120192 * 2
def baseEnd_4120192 : Nat := 52237997155793801569175

theorem tailTrace_4120192 : CollatzResearch.WordTrace tailWord_4120192 prefixEnd_4120192 52237997155793801569175 := by
  unfold tailWord_4120192
  simp only [CollatzResearch.WordTrace]
  refine ⟨75137873944627765808229415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100183831926170354410972553 75137873944627765808229415)
  ·
    refine ⟨112706810916941648712344123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75137873944627765808229415 112706810916941648712344123)
    ·
      refine ⟨169060216375412473068516185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112706810916941648712344123 169060216375412473068516185)
      ·
        refine ⟨126795162281559354801387139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169060216375412473068516185 126795162281559354801387139)
        ·
          refine ⟨190192743422339032202080709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126795162281559354801387139 190192743422339032202080709)
          ·
            refine ⟨35661139391688568537890133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190192743422339032202080709 35661139391688568537890133)
            ·
              refine ⟨52237997155793801569175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35661139391688568537890133 52237997155793801569175)
              ·
                rfl

theorem cell22_4120192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 11].length) (baseStart_4120192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120192 prefixEnd_4120192 := by exact prefixLift 4120192
  have htrace : WordTrace (prefixWord ++ tailWord_4120192) baseStart_4120192 baseEnd_4120192 := by
    simpa [prefixWord, tailWord_4120192, baseEnd_4120192] using wordTrace_append hprefix tailTrace_4120192
  have hstable : (prefixWord ++ tailWord_4120192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120192).length < 2 ^ (prefixWord ++ tailWord_4120192).sum := by decide
  have hdescent : baseEnd_4120192 < baseStart_4120192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_4120207 : Nat := 118140960795 + 4120207 * 2 ^ 59
def prefixEnd_4120207 : Nat := 4983230072969 + 3 ^ 40 * 4120207 * 2
def baseEnd_4120207 : Nat := 1410431058012977603242679

theorem tailTrace_4120207 : CollatzResearch.WordTrace tailWord_4120207 prefixEnd_4120207 1410431058012977603242679 := by
  unfold tailWord_4120207
  simp only [CollatzResearch.WordTrace]
  refine ⟨150276294984201189178254875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100184196656134126118836583 150276294984201189178254875)
  ·
    refine ⟨225414442476301783767382313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150276294984201189178254875 225414442476301783767382313)
    ·
      refine ⟨169060831857226337825536735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225414442476301783767382313 169060831857226337825536735)
      ·
        refine ⟨253591247785839506738305103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169060831857226337825536735 253591247785839506738305103)
        ·
          refine ⟨380386871678759260107457655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253591247785839506738305103 380386871678759260107457655)
          ·
            refine ⟨570580307518138890161186483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380386871678759260107457655 570580307518138890161186483)
            ·
              refine ⟨855870461277208335241779725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570580307518138890161186483 855870461277208335241779725)
              ·
                refine ⟨320951422978953125715667397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855870461277208335241779725 320951422978953125715667397)
                ·
                  refine ⟨60178391808553711071687637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320951422978953125715667397 60178391808553711071687637)
                  ·
                    refine ⟨1410431058012977603242679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60178391808553711071687637 1410431058012977603242679)
                    ·
                      rfl

theorem cell22_4120207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_4120207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120207 prefixEnd_4120207 := by exact prefixLift 4120207
  have htrace : WordTrace (prefixWord ++ tailWord_4120207) baseStart_4120207 baseEnd_4120207 := by
    simpa [prefixWord, tailWord_4120207, baseEnd_4120207] using wordTrace_append hprefix tailTrace_4120207
  have hstable : (prefixWord ++ tailWord_4120207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120207).length < 2 ^ (prefixWord ++ tailWord_4120207).sum := by decide
  have hdescent : baseEnd_4120207 < baseStart_4120207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120314 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_4120314 : Nat := 118140960795 + 4120314 * 2 ^ 59
def prefixEnd_4120314 : Nat := 4983230072969 + 3 ^ 40 * 4120314 * 2
def baseEnd_4120314 : Nat := 1410467686299664990817351

theorem tailTrace_4120314 : CollatzResearch.WordTrace tailWord_4120314 prefixEnd_4120314 1410467686299664990817351 := by
  unfold tailWord_4120314
  simp only [CollatzResearch.WordTrace]
  refine ⟨37570049398703386613099999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100186798396542364301599997 37570049398703386613099999)
  ·
    refine ⟨56355074098055079919649999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37570049398703386613099999 56355074098055079919649999)
    ·
      refine ⟨84532611147082619879474999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56355074098055079919649999 84532611147082619879474999)
      ·
        refine ⟨126798916720623929819212499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84532611147082619879474999 126798916720623929819212499)
        ·
          refine ⟨190198375080935894728818749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126798916720623929819212499 190198375080935894728818749)
          ·
            refine ⟨71324390655350960523307031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190198375080935894728818749 71324390655350960523307031)
            ·
              refine ⟨106986585983026440784960547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71324390655350960523307031 106986585983026440784960547)
              ·
                refine ⟨160479878974539661177440821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106986585983026440784960547 160479878974539661177440821)
                ·
                  refine ⟨15044988653863093235385077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160479878974539661177440821 15044988653863093235385077)
                  ·
                    refine ⟨1410467686299664990817351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15044988653863093235385077 1410467686299664990817351)
                    ·
                      rfl

theorem cell22_4120314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_4120314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120314 prefixEnd_4120314 := by exact prefixLift 4120314
  have htrace : WordTrace (prefixWord ++ tailWord_4120314) baseStart_4120314 baseEnd_4120314 := by
    simpa [prefixWord, tailWord_4120314, baseEnd_4120314] using wordTrace_append hprefix tailTrace_4120314
  have hstable : (prefixWord ++ tailWord_4120314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120314).length < 2 ^ (prefixWord ++ tailWord_4120314).sum := by decide
  have hdescent : baseEnd_4120314 < baseStart_4120314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120326 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4120326 : Nat := 118140960795 + 4120326 * 2 ^ 59
def prefixEnd_4120326 : Nat := 4983230072969 + 3 ^ 40 * 4120326 * 2
def baseEnd_4120326 : Nat := 1410471794144900959517315

theorem tailTrace_4120326 : CollatzResearch.WordTrace tailWord_4120326 prefixEnd_4120326 1410471794144900959517315 := by
  unfold tailWord_4120326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696269852211564765682401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100187090180513381667891221 4696269852211564765682401)
  ·
    refine ⟨3522202389158673574261801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4696269852211564765682401 3522202389158673574261801)
    ·
      refine ⟨2641651791869005180696351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3522202389158673574261801 2641651791869005180696351)
      ·
        refine ⟨3962477687803507771044527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641651791869005180696351 3962477687803507771044527)
        ·
          refine ⟨5943716531705261656566791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962477687803507771044527 5943716531705261656566791)
          ·
            refine ⟨8915574797557892484850187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943716531705261656566791 8915574797557892484850187)
            ·
              refine ⟨13373362196336838727275281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915574797557892484850187 13373362196336838727275281)
              ·
                refine ⟨10030021647252629045456461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13373362196336838727275281 10030021647252629045456461)
                ·
                  refine ⟨3761258117719735892046173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10030021647252629045456461 3761258117719735892046173)
                  ·
                    refine ⟨1410471794144900959517315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761258117719735892046173 1410471794144900959517315)
                    ·
                      rfl

theorem cell22_4120326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4120326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120326 prefixEnd_4120326 := by exact prefixLift 4120326
  have htrace : WordTrace (prefixWord ++ tailWord_4120326) baseStart_4120326 baseEnd_4120326 := by
    simpa [prefixWord, tailWord_4120326, baseEnd_4120326] using wordTrace_append hprefix tailTrace_4120326
  have hstable : (prefixWord ++ tailWord_4120326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120326).length < 2 ^ (prefixWord ++ tailWord_4120326).sum := by decide
  have hdescent : baseEnd_4120326 < baseStart_4120326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120329 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_4120329 : Nat := 118140960795 + 4120329 * 2 ^ 59
def prefixEnd_4120329 : Nat := 4983230072969 + 3 ^ 40 * 4120329 * 2
def baseEnd_4120329 : Nat := 1410472821106209951692305

theorem tailTrace_4120329 : CollatzResearch.WordTrace tailWord_4120329 prefixEnd_4120329 1410472821106209951692305 := by
  unfold tailWord_4120329
  simp only [CollatzResearch.WordTrace]
  refine ⟨150280744689759204014196041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100187163126506136009464027 150280744689759204014196041)
  ·
    refine ⟨112710558517319403010647031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150280744689759204014196041 112710558517319403010647031)
    ·
      refine ⟨169065837775979104515970547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112710558517319403010647031 169065837775979104515970547)
      ·
        refine ⟨253598756663968656773955821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169065837775979104515970547 253598756663968656773955821)
        ·
          refine ⟨95099533748988246290233433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253598756663968656773955821 95099533748988246290233433)
          ·
            refine ⟨71324650311741184717675075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95099533748988246290233433 71324650311741184717675075)
            ·
              refine ⟨106986975467611777076512613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71324650311741184717675075 106986975467611777076512613)
              ·
                refine ⟨20060057900177208201846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106986975467611777076512613 20060057900177208201846115)
                ·
                  refine ⟨30090086850265812302769173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20060057900177208201846115 30090086850265812302769173)
                  ·
                    refine ⟨1410472821106209951692305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30090086850265812302769173 1410472821106209951692305)
                    ·
                      rfl

theorem cell22_4120329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_4120329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120329 prefixEnd_4120329 := by exact prefixLift 4120329
  have htrace : WordTrace (prefixWord ++ tailWord_4120329) baseStart_4120329 baseEnd_4120329 := by
    simpa [prefixWord, tailWord_4120329, baseEnd_4120329] using wordTrace_append hprefix tailTrace_4120329
  have hstable : (prefixWord ++ tailWord_4120329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120329).length < 2 ^ (prefixWord ++ tailWord_4120329).sum := by decide
  have hdescent : baseEnd_4120329 < baseStart_4120329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120344 : List Nat := [2, 1, 2, 3, 1, 1, 2, 10]
def baseStart_4120344 : Nat := 118140960795 + 4120344 * 2 ^ 59
def prefixEnd_4120344 : Nat := 4983230072969 + 3 ^ 40 * 4120344 * 2
def baseEnd_4120344 : Nat := 156719772879194990285251

theorem tailTrace_4120344 : CollatzResearch.WordTrace tailWord_4120344 prefixEnd_4120344 156719772879194990285251 := by
  unfold tailWord_4120344
  simp only [CollatzResearch.WordTrace]
  refine ⟨75140645892352430787996043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100187527856469907717328057 75140645892352430787996043)
  ·
    refine ⟨112710968838528646181994065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75140645892352430787996043 112710968838528646181994065)
    ·
      refine ⟨84533226628896484636495549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112710968838528646181994065 84533226628896484636495549)
      ·
        refine ⟨31699959985836181738685831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84533226628896484636495549 31699959985836181738685831)
        ·
          refine ⟨47549939978754272608028747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31699959985836181738685831 47549939978754272608028747)
          ·
            refine ⟨71324909968131408912043121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47549939978754272608028747 71324909968131408912043121)
            ·
              refine ⟨53493682476098556684032341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71324909968131408912043121 53493682476098556684032341)
              ·
                refine ⟨156719772879194990285251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53493682476098556684032341 156719772879194990285251)
                ·
                  rfl

theorem cell22_4120344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_4120344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120344 prefixEnd_4120344 := by exact prefixLift 4120344
  have htrace : WordTrace (prefixWord ++ tailWord_4120344) baseStart_4120344 baseEnd_4120344 := by
    simpa [prefixWord, tailWord_4120344, baseEnd_4120344] using wordTrace_append hprefix tailTrace_4120344
  have hstable : (prefixWord ++ tailWord_4120344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120344).length < 2 ^ (prefixWord ++ tailWord_4120344).sum := by decide
  have hdescent : baseEnd_4120344 < baseStart_4120344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120346 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_4120346 : Nat := 118140960795 + 4120346 * 2 ^ 59
def prefixEnd_4120346 : Nat := 4983230072969 + 3 ^ 40 * 4120346 * 2
def baseEnd_4120346 : Nat := 1410478640553627574017253

theorem tailTrace_4120346 : CollatzResearch.WordTrace tailWord_4120346 prefixEnd_4120346 1410478640553627574017253 := by
  unfold tailWord_4120346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37570341182674403979391223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100187576487131743945043261 37570341182674403979391223)
  ·
    refine ⟨56355511774011605969086835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37570341182674403979391223 56355511774011605969086835)
    ·
      refine ⟨84533267661017408953630253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56355511774011605969086835 84533267661017408953630253)
      ·
        refine ⟨31699975372881528357611345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84533267661017408953630253 31699975372881528357611345)
        ·
          refine ⟨23774981529661146268208509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31699975372881528357611345 23774981529661146268208509)
          ·
            refine ⟨8915618073622929850578191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23774981529661146268208509 8915618073622929850578191)
            ·
              refine ⟨13373427110434394775867287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915618073622929850578191 13373427110434394775867287)
              ·
                refine ⟨20060140665651592163800931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13373427110434394775867287 20060140665651592163800931)
                ·
                  refine ⟨30090210998477388245701397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20060140665651592163800931 30090210998477388245701397)
                  ·
                    refine ⟨1410478640553627574017253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30090210998477388245701397 1410478640553627574017253)
                    ·
                      rfl

theorem cell22_4120346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_4120346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120346 prefixEnd_4120346 := by exact prefixLift 4120346
  have htrace : WordTrace (prefixWord ++ tailWord_4120346) baseStart_4120346 baseEnd_4120346 := by
    simpa [prefixWord, tailWord_4120346, baseEnd_4120346] using wordTrace_append hprefix tailTrace_4120346
  have hstable : (prefixWord ++ tailWord_4120346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120346).length < 2 ^ (prefixWord ++ tailWord_4120346).sum := by decide
  have hdescent : baseEnd_4120346 < baseStart_4120346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120382 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4120382 : Nat := 118140960795 + 4120382 * 2 ^ 59
def prefixEnd_4120382 : Nat := 4983230072969 + 3 ^ 40 * 4120382 * 2
def baseEnd_4120382 : Nat := 1410490964089335480117143

theorem tailTrace_4120382 : CollatzResearch.WordTrace tailWord_4120382 prefixEnd_4120382 1410490964089335480117143 := by
  unfold tailWord_4120382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785334719820899258234425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100188451839044796043916933 18785334719820899258234425)
  ·
    refine ⟨14089001039865674443675819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18785334719820899258234425 14089001039865674443675819)
    ·
      refine ⟨21133501559798511665513729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14089001039865674443675819 21133501559798511665513729)
      ·
        refine ⟨15850126169848883749135297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21133501559798511665513729 15850126169848883749135297)
        ·
          refine ⟨11887594627386662811851473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850126169848883749135297 11887594627386662811851473)
          ·
            refine ⟨8915695970539997108888605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11887594627386662811851473 8915695970539997108888605)
            ·
              refine ⟨3343385988952498915833227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8915695970539997108888605 3343385988952498915833227)
              ·
                refine ⟨5015078983428748373749841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343385988952498915833227 5015078983428748373749841)
                ·
                  refine ⟨3761309237571561280312381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015078983428748373749841 3761309237571561280312381)
                  ·
                    refine ⟨1410490964089335480117143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761309237571561280312381 1410490964089335480117143)
                    ·
                      rfl

theorem cell22_4120382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4120382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120382 prefixEnd_4120382 := by exact prefixLift 4120382
  have htrace : WordTrace (prefixWord ++ tailWord_4120382) baseStart_4120382 baseEnd_4120382 := by
    simpa [prefixWord, tailWord_4120382, baseEnd_4120382] using wordTrace_append hprefix tailTrace_4120382
  have hstable : (prefixWord ++ tailWord_4120382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120382).length < 2 ^ (prefixWord ++ tailWord_4120382).sum := by decide
  have hdescent : baseEnd_4120382 < baseStart_4120382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120478 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4120478 : Nat := 118140960795 + 4120478 * 2 ^ 59
def prefixEnd_4120478 : Nat := 4983230072969 + 3 ^ 40 * 4120478 * 2
def baseEnd_4120478 : Nat := 1410523826851223229716849

theorem tailTrace_4120478 : CollatzResearch.WordTrace tailWord_4120478 prefixEnd_4120478 1410523826851223229716849 := by
  unfold tailWord_4120478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785772395777425307671261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100190786110812934974246725 18785772395777425307671261)
  ·
    refine ⟨7044664648416534490376723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18785772395777425307671261 7044664648416534490376723)
    ·
      refine ⟨10566996972624801735565085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044664648416534490376723 10566996972624801735565085)
      ·
        refine ⟨3962623864734300650836907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10566996972624801735565085 3962623864734300650836907)
        ·
          refine ⟨5943935797101450976255361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962623864734300650836907 5943935797101450976255361)
          ·
            refine ⟨4457951847826088232191521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5943935797101450976255361 4457951847826088232191521)
            ·
              refine ⟨3343463885869566174143641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457951847826088232191521 3343463885869566174143641)
              ·
                refine ⟨2507597914402174630607731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343463885869566174143641 2507597914402174630607731)
                ·
                  refine ⟨3761396871603261945911597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507597914402174630607731 3761396871603261945911597)
                  ·
                    refine ⟨1410523826851223229716849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761396871603261945911597 1410523826851223229716849)
                    ·
                      rfl

theorem cell22_4120478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4120478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120478 prefixEnd_4120478 := by exact prefixLift 4120478
  have htrace : WordTrace (prefixWord ++ tailWord_4120478) baseStart_4120478 baseEnd_4120478 := by
    simpa [prefixWord, tailWord_4120478, baseEnd_4120478] using wordTrace_append hprefix tailTrace_4120478
  have hstable : (prefixWord ++ tailWord_4120478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120478).length < 2 ^ (prefixWord ++ tailWord_4120478).sum := by decide
  have hdescent : baseEnd_4120478 < baseStart_4120478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120596 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4120596 : Nat := 118140960795 + 4120596 * 2 ^ 59
def prefixEnd_4120596 : Nat := 4983230072969 + 3 ^ 40 * 4120596 * 2
def baseEnd_4120596 : Nat := 1410564220662710255266487

theorem tailTrace_4120596 : CollatzResearch.WordTrace tailWord_4120596 prefixEnd_4120596 1410564220662710255266487 := by
  unfold tailWord_4120596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75145241489895954307082821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100193655319861272409443761 75145241489895954307082821)
  ·
    refine ⟨14089732779355491432578029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75145241489895954307082821 14089732779355491432578029)
    ·
      refine ⟨5283649792258309287216761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14089732779355491432578029 5283649792258309287216761)
      ·
        refine ⟨3962737344193731965412571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283649792258309287216761 3962737344193731965412571)
        ·
          refine ⟨5944106016290597948118857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962737344193731965412571 5944106016290597948118857)
          ·
            refine ⟨4458079512217948461089143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944106016290597948118857 4458079512217948461089143)
            ·
              refine ⟨6687119268326922691633715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458079512217948461089143 6687119268326922691633715)
              ·
                refine ⟨10030678902490384037450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687119268326922691633715 10030678902490384037450573)
                ·
                  refine ⟨3761504588433894014043965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10030678902490384037450573 3761504588433894014043965)
                  ·
                    refine ⟨1410564220662710255266487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761504588433894014043965 1410564220662710255266487)
                    ·
                      rfl

theorem cell22_4120596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4120596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120596 prefixEnd_4120596 := by exact prefixLift 4120596
  have htrace : WordTrace (prefixWord ++ tailWord_4120596) baseStart_4120596 baseEnd_4120596 := by
    simpa [prefixWord, tailWord_4120596, baseEnd_4120596] using wordTrace_append hprefix tailTrace_4120596
  have hstable : (prefixWord ++ tailWord_4120596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120596).length < 2 ^ (prefixWord ++ tailWord_4120596).sum := by decide
  have hdescent : baseEnd_4120596 < baseStart_4120596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120609 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 5]
def baseStart_4120609 : Nat := 118140960795 + 4120609 * 2 ^ 59
def prefixEnd_4120609 : Nat := 4983230072969 + 3 ^ 40 * 4120609 * 2
def baseEnd_4120609 : Nat := 470189556942794184897149

theorem tailTrace_4120609 : CollatzResearch.WordTrace tailWord_4120609 prefixEnd_4120609 470189556942794184897149 := by
  unfold tailWord_4120609
  simp only [CollatzResearch.WordTrace]
  refine ⟨150290957128744811834388881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100193971419163207889592587 150290957128744811834388881)
  ·
    refine ⟨112718217846558608875791661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150290957128744811834388881 112718217846558608875791661)
    ·
      refine ⟨42269331692459478328421873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112718217846558608875791661 42269331692459478328421873)
      ·
        refine ⟨31701998769344608746316405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42269331692459478328421873 31701998769344608746316405)
        ·
          refine ⟨2972062384626057069967163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31701998769344608746316405 2972062384626057069967163)
          ·
            refine ⟨4458093576939085604950745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972062384626057069967163 4458093576939085604950745)
            ·
              refine ⟨3343570182704314203713059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458093576939085604950745 3343570182704314203713059)
              ·
                refine ⟨5015355274056471305569589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343570182704314203713059 5015355274056471305569589)
                ·
                  refine ⟨470189556942794184897149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5015355274056471305569589 470189556942794184897149)
                  ·
                    rfl

theorem cell22_4120609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_4120609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120609 prefixEnd_4120609 := by exact prefixLift 4120609
  have htrace : WordTrace (prefixWord ++ tailWord_4120609) baseStart_4120609 baseEnd_4120609 := by
    simpa [prefixWord, tailWord_4120609, baseEnd_4120609] using wordTrace_append hprefix tailTrace_4120609
  have hstable : (prefixWord ++ tailWord_4120609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120609).length < 2 ^ (prefixWord ++ tailWord_4120609).sum := by decide
  have hdescent : baseEnd_4120609 < baseStart_4120609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120622 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4120622 : Nat := 118140960795 + 4120622 * 2 ^ 59
def prefixEnd_4120622 : Nat := 4983230072969 + 3 ^ 40 * 4120622 * 2
def baseEnd_4120622 : Nat := 1410573120994054854116407

theorem tailTrace_4120622 : CollatzResearch.WordTrace tailWord_4120622 prefixEnd_4120622 1410573120994054854116407 := by
  unfold tailWord_4120622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786428909712214381826515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100194287518465143369741413 18786428909712214381826515)
  ·
    refine ⟨28179643364568321572739773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18786428909712214381826515 28179643364568321572739773)
    ·
      refine ⟨10567366261713120589777415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28179643364568321572739773 10567366261713120589777415)
      ·
        refine ⟨15851049392569680884666123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567366261713120589777415 15851049392569680884666123)
        ·
          refine ⟨23776574088854521326999185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15851049392569680884666123 23776574088854521326999185)
          ·
            refine ⟨17832430566640890995249389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23776574088854521326999185 17832430566640890995249389)
            ·
              refine ⟨6687161462490334123218521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17832430566640890995249389 6687161462490334123218521)
              ·
                refine ⟨5015371096867750592413891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687161462490334123218521 5015371096867750592413891)
                ·
                  refine ⟨7523056645301625888620837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015371096867750592413891 7523056645301625888620837)
                  ·
                    refine ⟨1410573120994054854116407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7523056645301625888620837 1410573120994054854116407)
                    ·
                      rfl

theorem cell22_4120622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4120622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120622 prefixEnd_4120622 := by exact prefixLift 4120622
  have htrace : WordTrace (prefixWord ++ tailWord_4120622) baseStart_4120622 baseEnd_4120622 := by
    simpa [prefixWord, tailWord_4120622, baseEnd_4120622] using wordTrace_append hprefix tailTrace_4120622
  have hstable : (prefixWord ++ tailWord_4120622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120622).length < 2 ^ (prefixWord ++ tailWord_4120622).sum := by decide
  have hdescent : baseEnd_4120622 < baseStart_4120622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120654 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4120654 : Nat := 118140960795 + 4120654 * 2 ^ 59
def prefixEnd_4120654 : Nat := 4983230072969 + 3 ^ 40 * 4120654 * 2
def baseEnd_4120654 : Nat := 470194691749339145772103

theorem tailTrace_4120654 : CollatzResearch.WordTrace tailWord_4120654 prefixEnd_4120654 470194691749339145772103 := by
  unfold tailWord_4120654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786574801697723064972127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100195065609054523013184677 18786574801697723064972127)
  ·
    refine ⟨28179862202546584597458191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18786574801697723064972127 28179862202546584597458191)
    ·
      refine ⟨42269793303819876896187287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28179862202546584597458191 42269793303819876896187287)
      ·
        refine ⟨63404689955729815344280931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42269793303819876896187287 63404689955729815344280931)
        ·
          refine ⟨95107034933594723016421397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63404689955729815344280931 95107034933594723016421397)
          ·
            refine ⟨4458142262512252641394753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95107034933594723016421397 4458142262512252641394753)
            ·
              refine ⟨3343606696884189481046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458142262512252641394753 3343606696884189481046065)
              ·
                refine ⟨2507705022663142110784549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343606696884189481046065 2507705022663142110784549)
                ·
                  refine ⟨470194691749339145772103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507705022663142110784549 470194691749339145772103)
                  ·
                    rfl

theorem cell22_4120654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4120654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120654 prefixEnd_4120654 := by exact prefixLift 4120654
  have htrace : WordTrace (prefixWord ++ tailWord_4120654) baseStart_4120654 baseEnd_4120654 := by
    simpa [prefixWord, tailWord_4120654, baseEnd_4120654] using wordTrace_append hprefix tailTrace_4120654
  have hstable : (prefixWord ++ tailWord_4120654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120654).length < 2 ^ (prefixWord ++ tailWord_4120654).sum := by decide
  have hdescent : baseEnd_4120654 < baseStart_4120654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120669 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4120669 : Nat := 118140960795 + 4120669 * 2 ^ 59
def prefixEnd_4120669 : Nat := 4983230072969 + 3 ^ 40 * 4120669 * 2
def baseEnd_4120669 : Nat := 1410589210054562398191263

theorem tailTrace_4120669 : CollatzResearch.WordTrace tailWord_4120669 prefixEnd_4120669 1410589210054562398191263 := by
  unfold tailWord_4120669
  simp only [CollatzResearch.WordTrace]
  refine ⟨150293145508527442081573061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100195430339018294721048707 150293145508527442081573061)
  ·
    refine ⟨28179964782848895390294949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150293145508527442081573061 28179964782848895390294949)
    ·
      refine ⟨5283743396784167885680303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28179964782848895390294949 5283743396784167885680303)
      ·
        refine ⟨7925615095176251828520455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283743396784167885680303 7925615095176251828520455)
        ·
          refine ⟨11888422642764377742780683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925615095176251828520455 11888422642764377742780683)
          ·
            refine ⟨17832633964146566614171025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888422642764377742780683 17832633964146566614171025)
            ·
              refine ⟨13374475473109924960628269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17832633964146566614171025 13374475473109924960628269)
              ·
                refine ⟨5015428302416221860235601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13374475473109924960628269 5015428302416221860235601)
                ·
                  refine ⟨3761571226812166395176701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015428302416221860235601 3761571226812166395176701)
                  ·
                    refine ⟨1410589210054562398191263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761571226812166395176701 1410589210054562398191263)
                    ·
                      rfl

theorem cell22_4120669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4120669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120669 prefixEnd_4120669 := by exact prefixLift 4120669
  have htrace : WordTrace (prefixWord ++ tailWord_4120669) baseStart_4120669 baseEnd_4120669 := by
    simpa [prefixWord, tailWord_4120669, baseEnd_4120669] using wordTrace_append hprefix tailTrace_4120669
  have hstable : (prefixWord ++ tailWord_4120669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120669).length < 2 ^ (prefixWord ++ tailWord_4120669).sum := by decide
  have hdescent : baseEnd_4120669 < baseStart_4120669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120682 : List Nat := [3, 1, 3, 2, 3, 1, 3, 6]
def baseStart_4120682 : Nat := 118140960795 + 4120682 * 2 ^ 59
def prefixEnd_4120682 : Nat := 4983230072969 + 3 ^ 40 * 4120682 * 2
def baseEnd_4120682 : Nat := 156732628913359410846247

theorem tailTrace_4120682 : CollatzResearch.WordTrace tailWord_4120682 prefixEnd_4120682 156732628913359410846247 := by
  unfold tailWord_4120682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573404914370086325449075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100195746438320230201197533 37573404914370086325449075)
  ·
    refine ⟨56360107371555129488173613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37573404914370086325449075 56360107371555129488173613)
    ·
      refine ⟨21135040264333173558065105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56360107371555129488173613 21135040264333173558065105)
      ·
        refine ⟨15851280198249880168548829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21135040264333173558065105 15851280198249880168548829)
        ·
          refine ⟨5944230074343705063205811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15851280198249880168548829 5944230074343705063205811)
          ·
            refine ⟨8916345111515557594808717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944230074343705063205811 8916345111515557594808717)
            ·
              refine ⟨3343629416818334098053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8916345111515557594808717 3343629416818334098053269)
              ·
                refine ⟨156732628913359410846247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3343629416818334098053269 156732628913359410846247)
                ·
                  rfl

theorem cell22_4120682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_4120682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120682 prefixEnd_4120682 := by exact prefixLift 4120682
  have htrace : WordTrace (prefixWord ++ tailWord_4120682) baseStart_4120682 baseEnd_4120682 := by
    simpa [prefixWord, tailWord_4120682, baseEnd_4120682] using wordTrace_append hprefix tailTrace_4120682
  have hstable : (prefixWord ++ tailWord_4120682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120682).length < 2 ^ (prefixWord ++ tailWord_4120682).sum := by decide
  have hdescent : baseEnd_4120682 < baseStart_4120682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120714 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_4120714 : Nat := 118140960795 + 4120714 * 2 ^ 59
def prefixEnd_4120714 : Nat := 4983230072969 + 3 ^ 40 * 4120714 * 2
def baseEnd_4120714 : Nat := 1410604614474197280816125

theorem tailTrace_4120714 : CollatzResearch.WordTrace tailWord_4120714 prefixEnd_4120714 1410604614474197280816125 := by
  unfold tailWord_4120714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573696698341103691740299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100196524528909609844640797 37573696698341103691740299)
  ·
    refine ⟨56360545047511655537610449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37573696698341103691740299 56360545047511655537610449)
    ·
      refine ⟨42270408785633741653207837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56360545047511655537610449 42270408785633741653207837)
      ·
        refine ⟨15851403294612653119952939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42270408785633741653207837 15851403294612653119952939)
        ·
          refine ⟨23777104941918979679929409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15851403294612653119952939 23777104941918979679929409)
          ·
            refine ⟨17832828706439234759947057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23777104941918979679929409 17832828706439234759947057)
            ·
              refine ⟨13374621529829426069960293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17832828706439234759947057 13374621529829426069960293)
              ·
                refine ⟨2507741536843017388117555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13374621529829426069960293 2507741536843017388117555)
                ·
                  refine ⟨3761612305264526082176333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507741536843017388117555 3761612305264526082176333)
                  ·
                    refine ⟨1410604614474197280816125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761612305264526082176333 1410604614474197280816125)
                    ·
                      rfl

theorem cell22_4120714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_4120714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120714 prefixEnd_4120714 := by exact prefixLift 4120714
  have htrace : WordTrace (prefixWord ++ tailWord_4120714) baseStart_4120714 baseEnd_4120714 := by
    simpa [prefixWord, tailWord_4120714, baseEnd_4120714] using wordTrace_append hprefix tailTrace_4120714
  have hstable : (prefixWord ++ tailWord_4120714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120714).length < 2 ^ (prefixWord ++ tailWord_4120714).sum := by decide
  have hdescent : baseEnd_4120714 < baseStart_4120714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120772 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_4120772 : Nat := 118140960795 + 4120772 * 2 ^ 59
def prefixEnd_4120772 : Nat := 4983230072969 + 3 ^ 40 * 4120772 * 2
def baseEnd_4120772 : Nat := 470208156353168154288649

theorem tailTrace_4120772 : CollatzResearch.WordTrace tailWord_4120772 prefixEnd_4120772 470208156353168154288649 := by
  unfold tailWord_4120772
  simp only [CollatzResearch.WordTrace]
  refine ⟨75148451113577145336286285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100197934818102860448381713 75148451113577145336286285)
  ·
    refine ⟨28180669167591429501107357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75148451113577145336286285 28180669167591429501107357)
    ·
      refine ⟨10567750937846786062915259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28180669167591429501107357 10567750937846786062915259)
      ·
        refine ⟨15851626406770179094372889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567750937846786062915259 15851626406770179094372889)
        ·
          refine ⟨11888719805077634320779667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15851626406770179094372889 11888719805077634320779667)
          ·
            refine ⟨17833079707616451481169501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888719805077634320779667 17833079707616451481169501)
            ·
              refine ⟨6687404890356169305438563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17833079707616451481169501 6687404890356169305438563)
              ·
                refine ⟨10031107335534253958157845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687404890356169305438563 10031107335534253958157845)
                ·
                  refine ⟨470208156353168154288649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10031107335534253958157845 470208156353168154288649)
                  ·
                    rfl

theorem cell22_4120772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_4120772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120772 prefixEnd_4120772 := by exact prefixLift 4120772
  have htrace : WordTrace (prefixWord ++ tailWord_4120772) baseStart_4120772 baseEnd_4120772 := by
    simpa [prefixWord, tailWord_4120772, baseEnd_4120772] using wordTrace_append hprefix tailTrace_4120772
  have hstable : (prefixWord ++ tailWord_4120772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120772).length < 2 ^ (prefixWord ++ tailWord_4120772).sum := by decide
  have hdescent : baseEnd_4120772 < baseStart_4120772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120834 : List Nat := [3, 4, 1, 1, 2, 3, 1, 7]
def baseStart_4120834 : Nat := 118140960795 + 4120834 * 2 ^ 59
def prefixEnd_4120834 : Nat := 4983230072969 + 3 ^ 40 * 4120834 * 2
def baseEnd_4120834 : Nat := 156738410325172996423973

theorem tailTrace_4120834 : CollatzResearch.WordTrace tailWord_4120834 prefixEnd_4120834 156738410325172996423973 := by
  unfold tailWord_4120834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574790888232418815332389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100199442368619783507553037 37574790888232418815332389)
  ·
    refine ⟨7045273291543578527874823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37574790888232418815332389 7045273291543578527874823)
    ·
      refine ⟨10567909937315367791812235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045273291543578527874823 10567909937315367791812235)
      ·
        refine ⟨15851864905973051687718353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567909937315367791812235 15851864905973051687718353)
        ·
          refine ⟨11888898679479788765788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15851864905973051687718353 11888898679479788765788765)
          ·
            refine ⟨4458337004804920787170787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11888898679479788765788765 4458337004804920787170787)
            ·
              refine ⟨6687505507207381180756181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458337004804920787170787 6687505507207381180756181)
              ·
                refine ⟨156738410325172996423973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6687505507207381180756181 156738410325172996423973)
                ·
                  rfl

theorem cell22_4120834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_4120834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120834 prefixEnd_4120834 := by exact prefixLift 4120834
  have htrace : WordTrace (prefixWord ++ tailWord_4120834) baseStart_4120834 baseEnd_4120834 := by
    simpa [prefixWord, tailWord_4120834, baseEnd_4120834] using wordTrace_append hprefix tailTrace_4120834
  have hstable : (prefixWord ++ tailWord_4120834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120834).length < 2 ^ (prefixWord ++ tailWord_4120834).sum := by decide
  have hdescent : baseEnd_4120834 < baseStart_4120834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4120860 : Nat := 118140960795 + 4120860 * 2 ^ 59
def prefixEnd_4120860 : Nat := 4983230072969 + 3 ^ 40 * 4120860 * 2
def baseEnd_4120860 : Nat := 1410654593257901566665677

theorem tailTrace_4120860 : CollatzResearch.WordTrace tailWord_4120860 prefixEnd_4120860 1410654593257901566665677 := by
  unfold tailWord_4120860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150055925417740850888017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100200074567223654467850689 75150055925417740850888017)
  ·
    refine ⟨56362541944063305638166013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75150055925417740850888017 56362541944063305638166013)
    ·
      refine ⟨21135953229023739614312255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56362541944063305638166013 21135953229023739614312255)
      ·
        refine ⟨31703929843535609421468383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135953229023739614312255 31703929843535609421468383)
        ·
          refine ⟨47555894765303414132202575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31703929843535609421468383 47555894765303414132202575)
          ·
            refine ⟨71333842147955121198303863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47555894765303414132202575 71333842147955121198303863)
            ·
              refine ⟨107000763221932681797455795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71333842147955121198303863 107000763221932681797455795)
              ·
                refine ⟨160501144832899022696183693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107000763221932681797455795 160501144832899022696183693)
                ·
                  refine ⟨60187929312337133511068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160501144832899022696183693 60187929312337133511068885)
                  ·
                    refine ⟨1410654593257901566665677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60187929312337133511068885 1410654593257901566665677)
                    ·
                      rfl

theorem cell22_4120860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4120860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120860 prefixEnd_4120860 := by exact prefixLift 4120860
  have htrace : WordTrace (prefixWord ++ tailWord_4120860) baseStart_4120860 baseEnd_4120860 := by
    simpa [prefixWord, tailWord_4120860, baseEnd_4120860] using wordTrace_append hprefix tailTrace_4120860
  have hstable : (prefixWord ++ tailWord_4120860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120860).length < 2 ^ (prefixWord ++ tailWord_4120860).sum := by decide
  have hdescent : baseEnd_4120860 < baseStart_4120860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120866 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_4120866 : Nat := 118140960795 + 4120866 * 2 ^ 59
def prefixEnd_4120866 : Nat := 4983230072969 + 3 ^ 40 * 4120866 * 2
def baseEnd_4120866 : Nat := 1410656647180519551015659

theorem tailTrace_4120866 : CollatzResearch.WordTrace tailWord_4120866 prefixEnd_4120866 1410656647180519551015659 := by
  unfold tailWord_4120866
  simp only [CollatzResearch.WordTrace]
  refine ⟨37575082672203436181623613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100200220459209163150996301 37575082672203436181623613)
  ·
    refine ⟨14090656002076288568108855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37575082672203436181623613 14090656002076288568108855)
    ·
      refine ⟨21135984003114432852163283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090656002076288568108855 21135984003114432852163283)
      ·
        refine ⟨31703976004671649278244925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135984003114432852163283 31703976004671649278244925)
        ·
          refine ⟨11888991001751868479341847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31703976004671649278244925 11888991001751868479341847)
          ·
            refine ⟨17833486502627802719012771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888991001751868479341847 17833486502627802719012771)
            ·
              refine ⟨26750229753941704078519157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17833486502627802719012771 26750229753941704078519157)
              ·
                refine ⟨2507834039432034757361171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26750229753941704078519157 2507834039432034757361171)
                ·
                  refine ⟨3761751059148052136041757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507834039432034757361171 3761751059148052136041757)
                  ·
                    refine ⟨1410656647180519551015659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761751059148052136041757 1410656647180519551015659)
                    ·
                      rfl

theorem cell22_4120866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_4120866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120866 prefixEnd_4120866 := by exact prefixLift 4120866
  have htrace : WordTrace (prefixWord ++ tailWord_4120866) baseStart_4120866 baseEnd_4120866 := by
    simpa [prefixWord, tailWord_4120866, baseEnd_4120866] using wordTrace_append hprefix tailTrace_4120866
  have hstable : (prefixWord ++ tailWord_4120866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120866).length < 2 ^ (prefixWord ++ tailWord_4120866).sum := by decide
  have hdescent : baseEnd_4120866 < baseStart_4120866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120937 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_4120937 : Nat := 118140960795 + 4120937 * 2 ^ 59
def prefixEnd_4120937 : Nat := 4983230072969 + 3 ^ 40 * 4120937 * 2
def baseEnd_4120937 : Nat := 1410680951931499032490441

theorem tailTrace_4120937 : CollatzResearch.WordTrace tailWord_4120937 prefixEnd_4120937 1410680951931499032490441 := by
  unfold tailWord_4120937
  simp only [CollatzResearch.WordTrace]
  refine ⟨150302920271556523852329065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100201946847704349234886043 150302920271556523852329065)
  ·
    refine ⟨112727190203667392889246799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150302920271556523852329065 112727190203667392889246799)
    ·
      refine ⟨169090785305501089333870199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112727190203667392889246799 169090785305501089333870199)
      ·
        refine ⟨253636177958251634000805299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169090785305501089333870199 253636177958251634000805299)
        ·
          refine ⟨380454266937377451001207949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253636177958251634000805299 380454266937377451001207949)
          ·
            refine ⟨142670350101516544125452981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380454266937377451001207949 142670350101516544125452981)
            ·
              refine ⟨13375345322017176011761217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142670350101516544125452981 13375345322017176011761217)
              ·
                refine ⟨10031508991512882008820913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13375345322017176011761217 10031508991512882008820913)
                ·
                  refine ⟨7523631743634661506615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031508991512882008820913 7523631743634661506615685)
                  ·
                    refine ⟨1410680951931499032490441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7523631743634661506615685 1410680951931499032490441)
                    ·
                      rfl

theorem cell22_4120937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_4120937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120937 prefixEnd_4120937 := by exact prefixLift 4120937
  have htrace : WordTrace (prefixWord ++ tailWord_4120937) baseStart_4120937 baseEnd_4120937 := by
    simpa [prefixWord, tailWord_4120937, baseEnd_4120937] using wordTrace_append hprefix tailTrace_4120937
  have hstable : (prefixWord ++ tailWord_4120937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120937).length < 2 ^ (prefixWord ++ tailWord_4120937).sum := by decide
  have hdescent : baseEnd_4120937 < baseStart_4120937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120941 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4120941 : Nat := 118140960795 + 4120941 * 2 ^ 59
def prefixEnd_4120941 : Nat := 4983230072969 + 3 ^ 40 * 4120941 * 2
def baseEnd_4120941 : Nat := 470227440404414785130143

theorem tailTrace_4120941 : CollatzResearch.WordTrace tailWord_4120941 prefixEnd_4120941 470227440404414785130143 := by
  unfold tailWord_4120941
  simp only [CollatzResearch.WordTrace]
  refine ⟨150303066163542032535474677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100202044109028021690316451 150303066163542032535474677)
  ·
    refine ⟨14090912452832065550200751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150303066163542032535474677 14090912452832065550200751)
    ·
      refine ⟨21136368679248098325301127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090912452832065550200751 21136368679248098325301127)
      ·
        refine ⟨31704553018872147487951691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136368679248098325301127 31704553018872147487951691)
        ·
          refine ⟨47556829528308221231927537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31704553018872147487951691 47556829528308221231927537)
          ·
            refine ⟨35667622146231165923945653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47556829528308221231927537 35667622146231165923945653)
            ·
              refine ⟨3343839576209171805369905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35667622146231165923945653 3343839576209171805369905)
              ·
                refine ⟨2507879682156878854027429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343839576209171805369905 2507879682156878854027429)
                ·
                  refine ⟨470227440404414785130143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507879682156878854027429 470227440404414785130143)
                  ·
                    rfl

theorem cell22_4120941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4120941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4120941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4120941 prefixEnd_4120941 := by exact prefixLift 4120941
  have htrace : WordTrace (prefixWord ++ tailWord_4120941) baseStart_4120941 baseEnd_4120941 := by
    simpa [prefixWord, tailWord_4120941, baseEnd_4120941] using wordTrace_append hprefix tailTrace_4120941
  have hstable : (prefixWord ++ tailWord_4120941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120941).length < 2 ^ (prefixWord ++ tailWord_4120941).sum := by decide
  have hdescent : baseEnd_4120941 < baseStart_4120941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121072 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_4121072 : Nat := 118140960795 + 4121072 * 2 ^ 59
def prefixEnd_4121072 : Nat := 4983230072969 + 3 ^ 40 * 4121072 * 2
def baseEnd_4121072 : Nat := 1410727165190403680365027

theorem tailTrace_4121072 : CollatzResearch.WordTrace tailWord_4121072 prefixEnd_4121072 1410727165190403680365027 := by
  unfold tailWord_4121072
  simp only [CollatzResearch.WordTrace]
  refine ⟨75153922063033720954246735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100205229417378294605662313 75153922063033720954246735)
  ·
    refine ⟨112730883094550581431370103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75153922063033720954246735 112730883094550581431370103)
    ·
      refine ⟨169096324641825872147055155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112730883094550581431370103 169096324641825872147055155)
      ·
        refine ⟨253644486962738808220582733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169096324641825872147055155 253644486962738808220582733)
        ·
          refine ⟨95116682611027053082718525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253644486962738808220582733 95116682611027053082718525)
          ·
            refine ⟨35668755979135144906019447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95116682611027053082718525 35668755979135144906019447)
            ·
              refine ⟨53503133968702717359029171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35668755979135144906019447 53503133968702717359029171)
              ·
                refine ⟨80254700953054076038543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53503133968702717359029171 80254700953054076038543757)
                ·
                  refine ⟨30095512857395278514453909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80254700953054076038543757 30095512857395278514453909)
                  ·
                    refine ⟨1410727165190403680365027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30095512857395278514453909 1410727165190403680365027)
                    ·
                      rfl

theorem cell22_4121072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_4121072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121072 prefixEnd_4121072 := by exact prefixLift 4121072
  have htrace : WordTrace (prefixWord ++ tailWord_4121072) baseStart_4121072 baseEnd_4121072 := by
    simpa [prefixWord, tailWord_4121072, baseEnd_4121072] using wordTrace_append hprefix tailTrace_4121072
  have hstable : (prefixWord ++ tailWord_4121072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121072).length < 2 ^ (prefixWord ++ tailWord_4121072).sum := by decide
  have hdescent : baseEnd_4121072 < baseStart_4121072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121087 : List Nat := [1, 1, 2, 2, 1, 2, 5, 8]
def baseStart_4121087 : Nat := 118140960795 + 4121087 * 2 ^ 59
def prefixEnd_4121087 : Nat := 4983230072969 + 3 ^ 40 * 4121087 * 2
def baseEnd_4121087 : Nat := 156748033332994293471109

theorem tailTrace_4121087 : CollatzResearch.WordTrace tailWord_4121087 prefixEnd_4121087 156748033332994293471109 := by
  unfold tailWord_4121087
  simp only [CollatzResearch.WordTrace]
  refine ⟨150308391221013099470289515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100205594147342066313526343 150308391221013099470289515)
  ·
    refine ⟨225462586831519649205434273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150308391221013099470289515 225462586831519649205434273)
    ·
      refine ⟨169096940123639736904075705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225462586831519649205434273 169096940123639736904075705)
      ·
        refine ⟨126822705092729802678056779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169096940123639736904075705 126822705092729802678056779)
        ·
          refine ⟨190234057639094704017085169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126822705092729802678056779 190234057639094704017085169)
          ·
            refine ⟨142675543229321028012813877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190234057639094704017085169 142675543229321028012813877)
            ·
              refine ⟨13375832177748846376201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142675543229321028012813877 13375832177748846376201301)
              ·
                refine ⟨156748033332994293471109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13375832177748846376201301 156748033332994293471109)
                ·
                  rfl

theorem cell22_4121087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 8].length) (baseStart_4121087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121087 prefixEnd_4121087 := by exact prefixLift 4121087
  have htrace : WordTrace (prefixWord ++ tailWord_4121087) baseStart_4121087 baseEnd_4121087 := by
    simpa [prefixWord, tailWord_4121087, baseEnd_4121087] using wordTrace_append hprefix tailTrace_4121087
  have hstable : (prefixWord ++ tailWord_4121087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121087).length < 2 ^ (prefixWord ++ tailWord_4121087).sum := by decide
  have hdescent : baseEnd_4121087 < baseStart_4121087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121089 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_4121089 : Nat := 118140960795 + 4121089 * 2 ^ 59
def prefixEnd_4121089 : Nat := 4983230072969 + 3 ^ 40 * 4121089 * 2
def baseEnd_4121089 : Nat := 1410732984637821302689975

theorem tailTrace_4121089 : CollatzResearch.WordTrace tailWord_4121089 prefixEnd_4121089 1410732984637821302689975 := by
  unfold tailWord_4121089
  simp only [CollatzResearch.WordTrace]
  refine ⟨150308464167005853811862321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100205642778003902541241547 150308464167005853811862321)
  ·
    refine ⟨112731348125254390358896741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150308464167005853811862321 112731348125254390358896741)
    ·
      refine ⟨21137127773485198192293139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112731348125254390358896741 21137127773485198192293139)
      ·
        refine ⟨31705691660227797288439709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21137127773485198192293139 31705691660227797288439709)
        ·
          refine ⟨11889634372585423983164891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31705691660227797288439709 11889634372585423983164891)
          ·
            refine ⟨17834451558878135974747337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889634372585423983164891 17834451558878135974747337)
            ·
              refine ⟨13375838669158601981060503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17834451558878135974747337 13375838669158601981060503)
              ·
                refine ⟨20063758003737902971590755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375838669158601981060503 20063758003737902971590755)
                ·
                  refine ⟨30095637005606854457386133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20063758003737902971590755 30095637005606854457386133)
                  ·
                    refine ⟨1410732984637821302689975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30095637005606854457386133 1410732984637821302689975)
                    ·
                      rfl

theorem cell22_4121089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_4121089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121089 prefixEnd_4121089 := by exact prefixLift 4121089
  have htrace : WordTrace (prefixWord ++ tailWord_4121089) baseStart_4121089 baseEnd_4121089 := by
    simpa [prefixWord, tailWord_4121089, baseEnd_4121089] using wordTrace_append hprefix tailTrace_4121089
  have hstable : (prefixWord ++ tailWord_4121089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121089).length < 2 ^ (prefixWord ++ tailWord_4121089).sum := by decide
  have hdescent : baseEnd_4121089 < baseStart_4121089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121108 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4121108 : Nat := 118140960795 + 4121108 * 2 ^ 59
def prefixEnd_4121108 : Nat := 4983230072969 + 3 ^ 40 * 4121108 * 2
def baseEnd_4121108 : Nat := 1410739488726111586464917

theorem tailTrace_4121108 : CollatzResearch.WordTrace tailWord_4121108 prefixEnd_4121108 1410739488726111586464917 := by
  unfold tailWord_4121108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75154578576968510028401989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100206104769291346704535985 75154578576968510028401989)
  ·
    refine ⟨14091483483181595630325373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75154578576968510028401989 14091483483181595630325373)
    ·
      refine ⟨5284306306193098361372015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14091483483181595630325373 5284306306193098361372015)
      ·
        refine ⟨7926459459289647542058023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284306306193098361372015 7926459459289647542058023)
        ·
          refine ⟨11889689188934471313087035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926459459289647542058023 11889689188934471313087035)
          ·
            refine ⟨17834533783401706969630553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889689188934471313087035 17834533783401706969630553)
            ·
              refine ⟨13375900337551280227222915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17834533783401706969630553 13375900337551280227222915)
              ·
                refine ⟨20063850506326920340834373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375900337551280227222915 20063850506326920340834373)
                ·
                  refine ⟨3761971969936297563906445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20063850506326920340834373 3761971969936297563906445)
                  ·
                    refine ⟨1410739488726111586464917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761971969936297563906445 1410739488726111586464917)
                    ·
                      rfl

theorem cell22_4121108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4121108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121108 prefixEnd_4121108 := by exact prefixLift 4121108
  have htrace : WordTrace (prefixWord ++ tailWord_4121108) baseStart_4121108 baseEnd_4121108 := by
    simpa [prefixWord, tailWord_4121108, baseEnd_4121108] using wordTrace_append hprefix tailTrace_4121108
  have hstable : (prefixWord ++ tailWord_4121108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121108).length < 2 ^ (prefixWord ++ tailWord_4121108).sum := by decide
  have hdescent : baseEnd_4121108 < baseStart_4121108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121140 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4121140 : Nat := 118140960795 + 4121140 * 2 ^ 59
def prefixEnd_4121140 : Nat := 4983230072969 + 3 ^ 40 * 4121140 * 2
def baseEnd_4121140 : Nat := 1410750442980074169664819

theorem tailTrace_4121140 : CollatzResearch.WordTrace tailWord_4121140 prefixEnd_4121140 1410750442980074169664819 := by
  unfold tailWord_4121140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155162144910544760984437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100206882859880726347979249 75155162144910544760984437)
  ·
    refine ⟨7045796451085363571342291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75155162144910544760984437 7045796451085363571342291)
    ·
      refine ⟨10568694676628045357013437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045796451085363571342291 10568694676628045357013437)
      ·
        refine ⟨3963260503735517008880039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10568694676628045357013437 3963260503735517008880039)
        ·
          refine ⟨5944890755603275513320059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963260503735517008880039 5944890755603275513320059)
          ·
            refine ⟨8917336133404913269980089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944890755603275513320059 8917336133404913269980089)
            ·
              refine ⟨6688002100053684952485067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8917336133404913269980089 6688002100053684952485067)
              ·
                refine ⟨10032003150080527428727601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688002100053684952485067 10032003150080527428727601)
                ·
                  refine ⟨7524002362560395571545701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032003150080527428727601 7524002362560395571545701)
                  ·
                    refine ⟨1410750442980074169664819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524002362560395571545701 1410750442980074169664819)
                    ·
                      rfl

theorem cell22_4121140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4121140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121140 prefixEnd_4121140 := by exact prefixLift 4121140
  have htrace : WordTrace (prefixWord ++ tailWord_4121140) baseStart_4121140 baseEnd_4121140 := by
    simpa [prefixWord, tailWord_4121140, baseEnd_4121140] using wordTrace_append hprefix tailTrace_4121140
  have hstable : (prefixWord ++ tailWord_4121140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121140).length < 2 ^ (prefixWord ++ tailWord_4121140).sum := by decide
  have hdescent : baseEnd_4121140 < baseStart_4121140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121164 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_4121164 : Nat := 118140960795 + 4121164 * 2 ^ 59
def prefixEnd_4121164 : Nat := 4983230072969 + 3 ^ 40 * 4121164 * 2
def baseEnd_4121164 : Nat := 1410758658670546107064745

theorem tailTrace_4121164 : CollatzResearch.WordTrace tailWord_4121164 prefixEnd_4121164 1410758658670546107064745 := by
  unfold tailWord_4121164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155599820867070810421273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100207466427822761080561697 75155599820867070810421273)
  ·
    refine ⟨56366699865650303107815955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75155599820867070810421273 56366699865650303107815955)
    ·
      refine ⟨84550049798475454661723933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56366699865650303107815955 84550049798475454661723933)
      ·
        refine ⟨31706268674428295498146475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84550049798475454661723933 31706268674428295498146475)
        ·
          refine ⟨47559403011642443247219713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31706268674428295498146475 47559403011642443247219713)
          ·
            refine ⟨35669552258731832435414785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47559403011642443247219713 35669552258731832435414785)
            ·
              refine ⟨26752164194048874326561089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35669552258731832435414785 26752164194048874326561089)
              ·
                refine ⟨20064123145536655744920817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26752164194048874326561089 20064123145536655744920817)
                ·
                  refine ⟨15048092359152491808690613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20064123145536655744920817 15048092359152491808690613)
                  ·
                    refine ⟨1410758658670546107064745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15048092359152491808690613 1410758658670546107064745)
                    ·
                      rfl

theorem cell22_4121164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_4121164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121164 prefixEnd_4121164 := by exact prefixLift 4121164
  have htrace : WordTrace (prefixWord ++ tailWord_4121164) baseStart_4121164 baseEnd_4121164 := by
    simpa [prefixWord, tailWord_4121164, baseEnd_4121164] using wordTrace_append hprefix tailTrace_4121164
  have hstable : (prefixWord ++ tailWord_4121164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121164).length < 2 ^ (prefixWord ++ tailWord_4121164).sum := by decide
  have hdescent : baseEnd_4121164 < baseStart_4121164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121213 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_4121213 : Nat := 118140960795 + 4121213 * 2 ^ 59
def prefixEnd_4121213 : Nat := 4983230072969 + 3 ^ 40 * 4121213 * 2
def baseEnd_4121213 : Nat := 1410775432371926312589595

theorem tailTrace_4121213 : CollatzResearch.WordTrace tailWord_4121213 prefixEnd_4121213 1410775432371926312589595 := by
  unfold tailWord_4121213
  simp only [CollatzResearch.WordTrace]
  refine ⟨150312986818556622989376293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100208657879037748659584195 150312986818556622989376293)
  ·
    refine ⟨28183685028479366810508055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150312986818556622989376293 28183685028479366810508055)
    ·
      refine ⟨42275527542719050215762083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28183685028479366810508055 42275527542719050215762083)
      ·
        refine ⟨63413291314078575323643125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42275527542719050215762083 63413291314078575323643125)
        ·
          refine ⟨5944996060694866436591543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63413291314078575323643125 5944996060694866436591543)
          ·
            refine ⟨8917494091042299654887315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944996060694866436591543 8917494091042299654887315)
            ·
              refine ⟨13376241136563449482330973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917494091042299654887315 13376241136563449482330973)
              ·
                refine ⟨5016090426211293555874115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13376241136563449482330973 5016090426211293555874115)
                ·
                  refine ⟨7524135639316940333811173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016090426211293555874115 7524135639316940333811173)
                  ·
                    refine ⟨1410775432371926312589595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524135639316940333811173 1410775432371926312589595)
                    ·
                      rfl

theorem cell22_4121213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_4121213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121213 prefixEnd_4121213 := by exact prefixLift 4121213
  have htrace : WordTrace (prefixWord ++ tailWord_4121213) baseStart_4121213 baseEnd_4121213 := by
    simpa [prefixWord, tailWord_4121213, baseEnd_4121213] using wordTrace_append hprefix tailTrace_4121213
  have hstable : (prefixWord ++ tailWord_4121213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121213).length < 2 ^ (prefixWord ++ tailWord_4121213).sum := by decide
  have hdescent : baseEnd_4121213 < baseStart_4121213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121239 : List Nat := [1, 1, 3, 3, 2, 1, 2, 9]
def baseStart_4121239 : Nat := 118140960795 + 4121239 * 2 ^ 59
def prefixEnd_4121239 : Nat := 4983230072969 + 3 ^ 40 * 4121239 * 2
def baseEnd_4121239 : Nat := 156753814744807879048835

theorem tailTrace_4121239 : CollatzResearch.WordTrace tailWord_4121239 prefixEnd_4121239 156753814744807879048835 := by
  unfold tailWord_4121239
  simp only [CollatzResearch.WordTrace]
  refine ⟨150313935116462429429822771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100209290077641619619881847 150313935116462429429822771)
  ·
    refine ⟨225470902674693644144734157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150313935116462429429822771 225470902674693644144734157)
    ·
      refine ⟨84551588503010116554275309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225470902674693644144734157 84551588503010116554275309)
      ·
        refine ⟨31706845688628793707853241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84551588503010116554275309 31706845688628793707853241)
        ·
          refine ⟨23780134266471595280889931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31706845688628793707853241 23780134266471595280889931)
          ·
            refine ⟨35670201399707392921334897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23780134266471595280889931 35670201399707392921334897)
            ·
              refine ⟨26752651049780544691001173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35670201399707392921334897 26752651049780544691001173)
              ·
                refine ⟨156753814744807879048835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26752651049780544691001173 156753814744807879048835)
                ·
                  rfl

theorem cell22_4121239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 9].length) (baseStart_4121239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121239 prefixEnd_4121239 := by exact prefixLift 4121239
  have htrace : WordTrace (prefixWord ++ tailWord_4121239) baseStart_4121239 baseEnd_4121239 := by
    simpa [prefixWord, tailWord_4121239, baseEnd_4121239] using wordTrace_append hprefix tailTrace_4121239
  have hstable : (prefixWord ++ tailWord_4121239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121239).length < 2 ^ (prefixWord ++ tailWord_4121239).sum := by decide
  have hdescent : baseEnd_4121239 < baseStart_4121239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121262 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_4121262 : Nat := 118140960795 + 4121262 * 2 ^ 59
def prefixEnd_4121262 : Nat := 4983230072969 + 3 ^ 40 * 4121262 * 2
def baseEnd_4121262 : Nat := 470264068691102172704815

theorem tailTrace_4121262 : CollatzResearch.WordTrace tailWord_4121262 prefixEnd_4121262 470264068691102172704815 := by
  unfold tailWord_4121262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18789346749422388044738755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100209849330252736238606693 18789346749422388044738755)
  ·
    refine ⟨28184020124133582067108133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18789346749422388044738755 28184020124133582067108133)
    ·
      refine ⟨5284503773275046637582775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28184020124133582067108133 5284503773275046637582775)
      ·
        refine ⟨7926755659912569956374163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284503773275046637582775 7926755659912569956374163)
        ·
          refine ⟨11890133489868854934561245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926755659912569956374163 11890133489868854934561245)
          ·
            refine ⟨4458800058700820600460467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11890133489868854934561245 4458800058700820600460467)
            ·
              refine ⟨6688200088051230900690701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458800058700820600460467 6688200088051230900690701)
              ·
                refine ⟨2508075033019211587759013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6688200088051230900690701 2508075033019211587759013)
                ·
                  refine ⟨470264068691102172704815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508075033019211587759013 470264068691102172704815)
                  ·
                    rfl

theorem cell22_4121262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_4121262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121262 prefixEnd_4121262 := by exact prefixLift 4121262
  have htrace : WordTrace (prefixWord ++ tailWord_4121262) baseStart_4121262 baseEnd_4121262 := by
    simpa [prefixWord, tailWord_4121262, baseEnd_4121262] using wordTrace_append hprefix tailTrace_4121262
  have hstable : (prefixWord ++ tailWord_4121262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121262).length < 2 ^ (prefixWord ++ tailWord_4121262).sum := by decide
  have hdescent : baseEnd_4121262 < baseStart_4121262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121288 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_4121288 : Nat := 118140960795 + 4121288 * 2 ^ 59
def prefixEnd_4121288 : Nat := 4983230072969 + 3 ^ 40 * 4121288 * 2
def baseEnd_4121288 : Nat := 1410801106404651116964365

theorem tailTrace_4121288 : CollatzResearch.WordTrace tailWord_4121288 prefixEnd_4121288 1410801106404651116964365 := by
  unfold tailWord_4121288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75157861146642455399178259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100210481528856607198904345 75157861146642455399178259)
  ·
    refine ⟨112736791719963683098767389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75157861146642455399178259 112736791719963683098767389)
    ·
      refine ⟨42276296894986381162037771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112736791719963683098767389 42276296894986381162037771)
      ·
        refine ⟨63414445342479571743056657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42276296894986381162037771 63414445342479571743056657)
        ·
          refine ⟨47560834006859678807292493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63414445342479571743056657 47560834006859678807292493)
          ·
            refine ⟨17835312752572379552734685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47560834006859678807292493 17835312752572379552734685)
            ·
              refine ⟨6688242282214642332275507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17835312752572379552734685 6688242282214642332275507)
              ·
                refine ⟨10032363423321963498413261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688242282214642332275507 10032363423321963498413261)
                ·
                  refine ⟨3762136283745736311904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10032363423321963498413261 3762136283745736311904973)
                  ·
                    refine ⟨1410801106404651116964365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762136283745736311904973 1410801106404651116964365)
                    ·
                      rfl

theorem cell22_4121288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_4121288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121288 prefixEnd_4121288 := by exact prefixLift 4121288
  have htrace : WordTrace (prefixWord ++ tailWord_4121288) baseStart_4121288 baseEnd_4121288 := by
    simpa [prefixWord, tailWord_4121288, baseEnd_4121288] using wordTrace_append hprefix tailTrace_4121288
  have hstable : (prefixWord ++ tailWord_4121288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121288).length < 2 ^ (prefixWord ++ tailWord_4121288).sum := by decide
  have hdescent : baseEnd_4121288 < baseStart_4121288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121361 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_4121361 : Nat := 118140960795 + 4121361 * 2 ^ 59
def prefixEnd_4121361 : Nat := 4983230072969 + 3 ^ 40 * 4121361 * 2
def baseEnd_4121361 : Nat := 1410826095796503259889141

theorem tailTrace_4121361 : CollatzResearch.WordTrace tailWord_4121361 prefixEnd_4121361 1410826095796503259889141 := by
  unfold tailWord_4121361
  simp only [CollatzResearch.WordTrace]
  refine ⟨150318384822020444265763937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100212256548013629510509291 150318384822020444265763937)
  ·
    refine ⟨112738788616515333199322953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150318384822020444265763937 112738788616515333199322953)
    ·
      refine ⟨84554091462386499899492215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112738788616515333199322953 84554091462386499899492215)
      ·
        refine ⟨126831137193579749849238323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84554091462386499899492215 126831137193579749849238323)
        ·
          refine ⟨190246705790369624773857485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126831137193579749849238323 190246705790369624773857485)
          ·
            refine ⟨71342514671388609290196557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190246705790369624773857485 71342514671388609290196557)
            ·
              refine ⟨26753443001770728483823709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71342514671388609290196557 26753443001770728483823709)
              ·
                refine ⟨10032541125664023181433891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26753443001770728483823709 10032541125664023181433891)
                ·
                  refine ⟨15048811688496034772150837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032541125664023181433891 15048811688496034772150837)
                  ·
                    refine ⟨1410826095796503259889141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15048811688496034772150837 1410826095796503259889141)
                    ·
                      rfl

theorem cell22_4121361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_4121361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121361 prefixEnd_4121361 := by exact prefixLift 4121361
  have htrace : WordTrace (prefixWord ++ tailWord_4121361) baseStart_4121361 baseEnd_4121361 := by
    simpa [prefixWord, tailWord_4121361, baseEnd_4121361] using wordTrace_append hprefix tailTrace_4121361
  have hstable : (prefixWord ++ tailWord_4121361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121361).length < 2 ^ (prefixWord ++ tailWord_4121361).sum := by decide
  have hdescent : baseEnd_4121361 < baseStart_4121361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121378 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4121378 : Nat := 118140960795 + 4121378 * 2 ^ 59
def prefixEnd_4121378 : Nat := 4983230072969 + 3 ^ 40 * 4121378 * 2
def baseEnd_4121378 : Nat := 1410831915243920882214089

theorem tailTrace_4121378 : CollatzResearch.WordTrace tailWord_4121378 prefixEnd_4121378 1410831915243920882214089 := by
  unfold tailWord_4121378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37579751215739714042283197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100212669908639237446088525 37579751215739714042283197)
  ·
    refine ⟨14092406705902392765856199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37579751215739714042283197 14092406705902392765856199)
    ·
      refine ⟨21138610058853589148784299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092406705902392765856199 21138610058853589148784299)
      ·
        refine ⟨31707915088280383723176449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21138610058853589148784299 31707915088280383723176449)
        ·
          refine ⟨23780936316210287792382337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31707915088280383723176449 23780936316210287792382337)
          ·
            refine ⟨17835702237157715844286753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23780936316210287792382337 17835702237157715844286753)
            ·
              refine ⟨13376776677868286883215065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17835702237157715844286753 13376776677868286883215065)
              ·
                refine ⟨10032582508401215162411299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13376776677868286883215065 10032582508401215162411299)
                ·
                  refine ⟨15048873762601822743616949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032582508401215162411299 15048873762601822743616949)
                  ·
                    refine ⟨1410831915243920882214089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15048873762601822743616949 1410831915243920882214089)
                    ·
                      rfl

theorem cell22_4121378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4121378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121378 prefixEnd_4121378 := by exact prefixLift 4121378
  have htrace : WordTrace (prefixWord ++ tailWord_4121378) baseStart_4121378 baseEnd_4121378 := by
    simpa [prefixWord, tailWord_4121378, baseEnd_4121378] using wordTrace_append hprefix tailTrace_4121378
  have hstable : (prefixWord ++ tailWord_4121378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121378).length < 2 ^ (prefixWord ++ tailWord_4121378).sum := by decide
  have hdescent : baseEnd_4121378 < baseStart_4121378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121395 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 2, 3]
def baseStart_4121395 : Nat := 118140960795 + 4121395 * 2 ^ 59
def prefixEnd_4121395 : Nat := 4983230072969 + 3 ^ 40 * 4121395 * 2
def baseEnd_4121395 : Nat := 1410837734691338504539037

theorem tailTrace_4121395 : CollatzResearch.WordTrace tailWord_4121395 prefixEnd_4121395 1410837734691338504539037 := by
  unfold tailWord_4121395
  simp only [CollatzResearch.WordTrace]
  refine ⟨150319624903897268072501639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100213083269264845381667759 150319624903897268072501639)
  ·
    refine ⟨225479437355845902108752459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150319624903897268072501639 225479437355845902108752459)
    ·
      refine ⟨338219156033768853163128689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225479437355845902108752459 338219156033768853163128689)
      ·
        refine ⟨253664367025326639872346517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338219156033768853163128689 253664367025326639872346517)
        ·
          refine ⟨11890517204312186244016243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253664367025326639872346517 11890517204312186244016243)
          ·
            refine ⟨17835775806468279366024365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890517204312186244016243 17835775806468279366024365)
            ·
              refine ⟨6688415927425604762259137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17835775806468279366024365 6688415927425604762259137)
              ·
                refine ⟨5016311945569203571694353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6688415927425604762259137 5016311945569203571694353)
                ·
                  refine ⟨3762233959176902678770765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016311945569203571694353 3762233959176902678770765)
                  ·
                    refine ⟨1410837734691338504539037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762233959176902678770765 1410837734691338504539037)
                    ·
                      rfl

theorem cell22_4121395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].length) (baseStart_4121395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121395 prefixEnd_4121395 := by exact prefixLift 4121395
  have htrace : WordTrace (prefixWord ++ tailWord_4121395) baseStart_4121395 baseEnd_4121395 := by
    simpa [prefixWord, tailWord_4121395, baseEnd_4121395] using wordTrace_append hprefix tailTrace_4121395
  have hstable : (prefixWord ++ tailWord_4121395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121395).length < 2 ^ (prefixWord ++ tailWord_4121395).sum := by decide
  have hdescent : baseEnd_4121395 < baseStart_4121395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121425 : List Nat := [1, 2, 2, 1, 6, 2, 2, 6]
def baseStart_4121425 : Nat := 118140960795 + 4121425 * 2 ^ 59
def prefixEnd_4121425 : Nat := 4983230072969 + 3 ^ 40 * 4121425 * 2
def baseEnd_4121425 : Nat := 156760889367158714032105

theorem tailTrace_4121425 : CollatzResearch.WordTrace tailWord_4121425 prefixEnd_4121425 156760889367158714032105 := by
  unfold tailWord_4121425
  simp only [CollatzResearch.WordTrace]
  refine ⟨150320719093788583196093729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100213812729192388797395819 150320719093788583196093729)
  ·
    refine ⟨112740539320341437397070297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150320719093788583196093729 112740539320341437397070297)
    ·
      refine ⟨84555404490256078047802723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112740539320341437397070297 84555404490256078047802723)
      ·
        refine ⟨126833106735384117071704085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84555404490256078047802723 126833106735384117071704085)
        ·
          refine ⟨5945301878221130487736129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126833106735384117071704085 5945301878221130487736129)
          ·
            refine ⟨4458976408665847865802097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945301878221130487736129 4458976408665847865802097)
            ·
              refine ⟨3344232306499385899351573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458976408665847865802097 3344232306499385899351573)
              ·
                refine ⟨156760889367158714032105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3344232306499385899351573 156760889367158714032105)
                ·
                  rfl

theorem cell22_4121425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 6].length) (baseStart_4121425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121425 prefixEnd_4121425 := by exact prefixLift 4121425
  have htrace : WordTrace (prefixWord ++ tailWord_4121425) baseStart_4121425 baseEnd_4121425 := by
    simpa [prefixWord, tailWord_4121425, baseEnd_4121425] using wordTrace_append hprefix tailTrace_4121425
  have hstable : (prefixWord ++ tailWord_4121425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121425).length < 2 ^ (prefixWord ++ tailWord_4121425).sum := by decide
  have hdescent : baseEnd_4121425 < baseStart_4121425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121451 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_4121451 : Nat := 118140960795 + 4121451 * 2 ^ 59
def prefixEnd_4121451 : Nat := 4983230072969 + 3 ^ 40 * 4121451 * 2
def baseEnd_4121451 : Nat := 1410856904635773025138865

theorem tailTrace_4121451 : CollatzResearch.WordTrace tailWord_4121451 prefixEnd_4121451 1410856904635773025138865 := by
  unfold tailWord_4121451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150321667391694389636540207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100214444927796259757693471 150321667391694389636540207)
  ·
    refine ⟨225482501087541584454810311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150321667391694389636540207 225482501087541584454810311)
    ·
      refine ⟨338223751631312376682215467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225482501087541584454810311 338223751631312376682215467)
      ·
        refine ⟨507335627446968565023323201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338223751631312376682215467 507335627446968565023323201)
        ·
          refine ⟨380501720585226423767492401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507335627446968565023323201 380501720585226423767492401)
          ·
            refine ⟨285376290438919817825619301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380501720585226423767492401 285376290438919817825619301)
            ·
              refine ⟨53508054457297465842303619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285376290438919817825619301 53508054457297465842303619)
              ·
                refine ⟨80262081685946198763455429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53508054457297465842303619 80262081685946198763455429)
                ·
                  refine ⟨15049140316114912268147893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80262081685946198763455429 15049140316114912268147893)
                  ·
                    refine ⟨1410856904635773025138865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15049140316114912268147893 1410856904635773025138865)
                    ·
                      rfl

theorem cell22_4121451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_4121451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121451 prefixEnd_4121451 := by exact prefixLift 4121451
  have htrace : WordTrace (prefixWord ++ tailWord_4121451) baseStart_4121451 baseEnd_4121451 := by
    simpa [prefixWord, tailWord_4121451, baseEnd_4121451] using wordTrace_append hprefix tailTrace_4121451
  have hstable : (prefixWord ++ tailWord_4121451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121451).length < 2 ^ (prefixWord ++ tailWord_4121451).sum := by decide
  have hdescent : baseEnd_4121451 < baseStart_4121451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121453 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4121453 : Nat := 118140960795 + 4121453 * 2 ^ 59
def prefixEnd_4121453 : Nat := 4983230072969 + 3 ^ 40 * 4121453 * 2
def baseEnd_4121453 : Nat := 470285863092215228862953

theorem tailTrace_4121453 : CollatzResearch.WordTrace tailWord_4121453 prefixEnd_4121453 470285863092215228862953 := by
  unfold tailWord_4121453
  simp only [CollatzResearch.WordTrace]
  refine ⟨150321740337687143978113013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100214493558458095985408675 150321740337687143978113013)
  ·
    refine ⟨14092663156658169747948095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150321740337687143978113013 14092663156658169747948095)
    ·
      refine ⟨21138994734987254621922143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092663156658169747948095 21138994734987254621922143)
      ·
        refine ⟨31708492102480881932883215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21138994734987254621922143 31708492102480881932883215)
        ·
          refine ⟨47562738153721322899324823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31708492102480881932883215 47562738153721322899324823)
          ·
            refine ⟨71344107230581984348987235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47562738153721322899324823 71344107230581984348987235)
            ·
              refine ⟨107016160845872976523480853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71344107230581984348987235 107016160845872976523480853)
              ·
                refine ⟨5016382539650295774538165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107016160845872976523480853 5016382539650295774538165)
                ·
                  refine ⟨470285863092215228862953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016382539650295774538165 470285863092215228862953)
                  ·
                    rfl

theorem cell22_4121453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4121453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121453 prefixEnd_4121453 := by exact prefixLift 4121453
  have htrace : WordTrace (prefixWord ++ tailWord_4121453) baseStart_4121453 baseEnd_4121453 := by
    simpa [prefixWord, tailWord_4121453, baseEnd_4121453] using wordTrace_append hprefix tailTrace_4121453
  have hstable : (prefixWord ++ tailWord_4121453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121453).length < 2 ^ (prefixWord ++ tailWord_4121453).sum := by decide
  have hdescent : baseEnd_4121453 < baseStart_4121453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121466 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_4121466 : Nat := 118140960795 + 4121466 * 2 ^ 59
def prefixEnd_4121466 : Nat := 4983230072969 + 3 ^ 40 * 4121466 * 2
def baseEnd_4121466 : Nat := 1410862039442317986013819

theorem tailTrace_4121466 : CollatzResearch.WordTrace tailWord_4121466 prefixEnd_4121466 1410862039442317986013819 := by
  unfold tailWord_4121466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580553621660011799584063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100214809657760031465557501 37580553621660011799584063)
  ·
    refine ⟨56370830432490017699376095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37580553621660011799584063 56370830432490017699376095)
    ·
      refine ⟨84556245648735026549064143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56370830432490017699376095 84556245648735026549064143)
      ·
        refine ⟨126834368473102539823596215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84556245648735026549064143 126834368473102539823596215)
        ·
          refine ⟨190251552709653809735394323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126834368473102539823596215 190251552709653809735394323)
          ·
            refine ⟨285377329064480714603091485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190251552709653809735394323 285377329064480714603091485)
            ·
              refine ⟨107016498399180267976159307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285377329064480714603091485 107016498399180267976159307)
              ·
                refine ⟨160524747598770401964238961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107016498399180267976159307 160524747598770401964238961)
                ·
                  refine ⟨120393560699077801473179221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160524747598770401964238961 120393560699077801473179221)
                  ·
                    refine ⟨1410862039442317986013819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120393560699077801473179221 1410862039442317986013819)
                    ·
                      rfl

theorem cell22_4121466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_4121466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121466 prefixEnd_4121466 := by exact prefixLift 4121466
  have htrace : WordTrace (prefixWord ++ tailWord_4121466) baseStart_4121466 baseEnd_4121466 := by
    simpa [prefixWord, tailWord_4121466, baseEnd_4121466] using wordTrace_append hprefix tailTrace_4121466
  have hstable : (prefixWord ++ tailWord_4121466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121466).length < 2 ^ (prefixWord ++ tailWord_4121466).sum := by decide
  have hdescent : baseEnd_4121466 < baseStart_4121466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121530 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_4121530 : Nat := 118140960795 + 4121530 * 2 ^ 59
def prefixEnd_4121530 : Nat := 4983230072969 + 3 ^ 40 * 4121530 * 2
def baseEnd_4121530 : Nat := 1410883947950243152413623

theorem tailTrace_4121530 : CollatzResearch.WordTrace tailWord_4121530 prefixEnd_4121530 1410883947950243152413623 := by
  unfold tailWord_4121530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581137189602046532166511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100216365838938790752444029 37581137189602046532166511)
  ·
    refine ⟨56371705784403069798249767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37581137189602046532166511 56371705784403069798249767)
    ·
      refine ⟨84557558676604604697374651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56371705784403069798249767 84557558676604604697374651)
      ·
        refine ⟨126836338014906907046061977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84557558676604604697374651 126836338014906907046061977)
        ·
          refine ⟨95127253511180180284546483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126836338014906907046061977 95127253511180180284546483)
          ·
            refine ⟨142690880266770270426819725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95127253511180180284546483 142690880266770270426819725)
            ·
              refine ⟨53509080100038851410057397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142690880266770270426819725 53509080100038851410057397)
              ·
                refine ⟨5016476259378642319692881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53509080100038851410057397 5016476259378642319692881)
                ·
                  refine ⟨3762357194533981739769661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016476259378642319692881 3762357194533981739769661)
                  ·
                    refine ⟨1410883947950243152413623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762357194533981739769661 1410883947950243152413623)
                    ·
                      rfl

theorem cell22_4121530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_4121530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121530 prefixEnd_4121530 := by exact prefixLift 4121530
  have htrace : WordTrace (prefixWord ++ tailWord_4121530) baseStart_4121530 baseEnd_4121530 := by
    simpa [prefixWord, tailWord_4121530, baseEnd_4121530] using wordTrace_append hprefix tailTrace_4121530
  have hstable : (prefixWord ++ tailWord_4121530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121530).length < 2 ^ (prefixWord ++ tailWord_4121530).sum := by decide
  have hdescent : baseEnd_4121530 < baseStart_4121530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121639 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 5]
def baseStart_4121639 : Nat := 118140960795 + 4121639 * 2 ^ 59
def prefixEnd_4121639 : Nat := 4983230072969 + 3 ^ 40 * 4121639 * 2
def baseEnd_4121639 : Nat := 470307086959267733812763

theorem tailTrace_4121639 : CollatzResearch.WordTrace tailWord_4121639 prefixEnd_4121639 470307086959267733812763 := by
  unfold tailWord_4121639
  simp only [CollatzResearch.WordTrace]
  refine ⟨150328524315013297744383971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100219016210008865162922647 150328524315013297744383971)
  ·
    refine ⟨225492786472519946616575957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150328524315013297744383971 225492786472519946616575957)
    ·
      refine ⟨5284987182949686248825999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225492786472519946616575957 5284987182949686248825999)
      ·
        refine ⟨7927480774424529373238999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284987182949686248825999 7927480774424529373238999)
        ·
          refine ⟨11891221161636794059858499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927480774424529373238999 11891221161636794059858499)
          ·
            refine ⟨17836831742455191089787749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891221161636794059858499 17836831742455191089787749)
            ·
              refine ⟨3344405951710348329335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17836831742455191089787749 3344405951710348329335203)
              ·
                refine ⟨5016608927565522494002805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344405951710348329335203 5016608927565522494002805)
                ·
                  refine ⟨470307086959267733812763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016608927565522494002805 470307086959267733812763)
                  ·
                    rfl

theorem cell22_4121639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 5].length) (baseStart_4121639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121639 prefixEnd_4121639 := by exact prefixLift 4121639
  have htrace : WordTrace (prefixWord ++ tailWord_4121639) baseStart_4121639 baseEnd_4121639 := by
    simpa [prefixWord, tailWord_4121639, baseEnd_4121639] using wordTrace_append hprefix tailTrace_4121639
  have hstable : (prefixWord ++ tailWord_4121639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121639).length < 2 ^ (prefixWord ++ tailWord_4121639).sum := by decide
  have hdescent : baseEnd_4121639 < baseStart_4121639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121684 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_4121684 : Nat := 118140960795 + 4121684 * 2 ^ 59
def prefixEnd_4121684 : Nat := 4983230072969 + 3 ^ 40 * 4121684 * 2
def baseEnd_4121684 : Nat := 470312221765812694687717

theorem tailTrace_4121684 : CollatzResearch.WordTrace tailWord_4121684 prefixEnd_4121684 470312221765812694687717 := by
  unfold tailWord_4121684
  simp only [CollatzResearch.WordTrace]
  refine ⟨75165082799925135214886053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100220110399900180286514737 75165082799925135214886053)
  ·
    refine ⟨14093453024985962852791135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75165082799925135214886053 14093453024985962852791135)
    ·
      refine ⟨21140179537478944279186703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14093453024985962852791135 21140179537478944279186703)
      ·
        refine ⟨31710269306218416418780055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21140179537478944279186703 31710269306218416418780055)
        ·
          refine ⟨47565403959327624628170083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710269306218416418780055 47565403959327624628170083)
          ·
            refine ⟨71348105938991436942255125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47565403959327624628170083 71348105938991436942255125)
            ·
              refine ⟨3344442465890223606668209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71348105938991436942255125 3344442465890223606668209)
              ·
                refine ⟨2508331849417667705001157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344442465890223606668209 2508331849417667705001157)
                ·
                  refine ⟨470312221765812694687717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508331849417667705001157 470312221765812694687717)
                  ·
                    rfl

theorem cell22_4121684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_4121684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121684 prefixEnd_4121684 := by exact prefixLift 4121684
  have htrace : WordTrace (prefixWord ++ tailWord_4121684) baseStart_4121684 baseEnd_4121684 := by
    simpa [prefixWord, tailWord_4121684, baseEnd_4121684] using wordTrace_append hprefix tailTrace_4121684
  have hstable : (prefixWord ++ tailWord_4121684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121684).length < 2 ^ (prefixWord ++ tailWord_4121684).sum := by decide
  have hdescent : baseEnd_4121684 < baseStart_4121684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121802 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_4121802 : Nat := 118140960795 + 4121802 * 2 ^ 59
def prefixEnd_4121802 : Nat := 4983230072969 + 3 ^ 40 * 4121802 * 2
def baseEnd_4121802 : Nat := 470325686369641703204263

theorem tailTrace_4121802 : CollatzResearch.WordTrace tailWord_4121802 prefixEnd_4121802 470325686369641703204263 := by
  unfold tailWord_4121802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37583617353355694145641915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100222979608948517721711773 37583617353355694145641915)
  ·
    refine ⟨56375426030033541218462873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37583617353355694145641915 56375426030033541218462873)
    ·
      refine ⟨42281569522525155913847155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56375426030033541218462873 42281569522525155913847155)
      ·
        refine ⟨63422354283787733870770733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42281569522525155913847155 63422354283787733870770733)
        ·
          refine ⟨23783382856420400201539025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63422354283787733870770733 23783382856420400201539025)
          ·
            refine ⟨17837537142315300151154269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23783382856420400201539025 17837537142315300151154269)
            ·
              refine ⟨6689076428368237556682851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17837537142315300151154269 6689076428368237556682851)
              ·
                refine ⟨10033614642552356335024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689076428368237556682851 10033614642552356335024277)
                ·
                  refine ⟨470325686369641703204263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10033614642552356335024277 470325686369641703204263)
                  ·
                    rfl

theorem cell22_4121802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_4121802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121802 prefixEnd_4121802 := by exact prefixLift 4121802
  have htrace : WordTrace (prefixWord ++ tailWord_4121802) baseStart_4121802 baseEnd_4121802 := by
    simpa [prefixWord, tailWord_4121802, baseEnd_4121802] using wordTrace_append hprefix tailTrace_4121802
  have hstable : (prefixWord ++ tailWord_4121802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121802).length < 2 ^ (prefixWord ++ tailWord_4121802).sum := by decide
  have hdescent : baseEnd_4121802 < baseStart_4121802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121815 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_4121815 : Nat := 118140960795 + 4121815 * 2 ^ 59
def prefixEnd_4121815 : Nat := 4983230072969 + 3 ^ 40 * 4121815 * 2
def baseEnd_4121815 : Nat := 1410981509274597409037749

theorem tailTrace_4121815 : CollatzResearch.WordTrace tailWord_4121815 prefixEnd_4121815 1410981509274597409037749 := by
  unfold tailWord_4121815
  simp only [CollatzResearch.WordTrace]
  refine ⟨150334943562375679802790899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100223295708250453201860599 150334943562375679802790899)
  ·
    refine ⟨225502415343563519704186349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150334943562375679802790899 225502415343563519704186349)
    ·
      refine ⟨84563405753836319889069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225502415343563519704186349 84563405753836319889069881)
      ·
        refine ⟨63422554315377239916802411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84563405753836319889069881 63422554315377239916802411)
        ·
          refine ⟨95133831473065859875203617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63422554315377239916802411 95133831473065859875203617)
          ·
            refine ⟨71350373604799394906402713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95133831473065859875203617 71350373604799394906402713)
            ·
              refine ⟨53512780203599546179802035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71350373604799394906402713 53512780203599546179802035)
              ·
                refine ⟨80269170305399319269703053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53512780203599546179802035 80269170305399319269703053)
                ·
                  refine ⟨30100938864524744726138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80269170305399319269703053 30100938864524744726138645)
                  ·
                    refine ⟨1410981509274597409037749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30100938864524744726138645 1410981509274597409037749)
                    ·
                      rfl

theorem cell22_4121815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_4121815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121815 prefixEnd_4121815 := by exact prefixLift 4121815
  have htrace : WordTrace (prefixWord ++ tailWord_4121815) baseStart_4121815 baseEnd_4121815 := by
    simpa [prefixWord, tailWord_4121815, baseEnd_4121815] using wordTrace_append hprefix tailTrace_4121815
  have hstable : (prefixWord ++ tailWord_4121815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121815).length < 2 ^ (prefixWord ++ tailWord_4121815).sum := by decide
  have hdescent : baseEnd_4121815 < baseStart_4121815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121864 : List Nat := [2, 1, 3, 2, 4, 2, 1, 7]
def baseStart_4121864 : Nat := 118140960795 + 4121864 * 2 ^ 59
def prefixEnd_4121864 : Nat := 4983230072969 + 3 ^ 40 * 4121864 * 2
def baseEnd_4121864 : Nat := 156777586997330846062511

theorem tailTrace_4121864 : CollatzResearch.WordTrace tailWord_4121864 prefixEnd_4121864 156777586997330846062511 := by
  unfold tailWord_4121864
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168365369599080585662323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100224487159465440780883097 75168365369599080585662323)
  ·
    refine ⟨112752548054398620878493485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75168365369599080585662323 112752548054398620878493485)
    ·
      refine ⟨42282205520399482829435057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112752548054398620878493485 42282205520399482829435057)
      ·
        refine ⟨31711654140299612122076293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42282205520399482829435057 31711654140299612122076293)
        ·
          refine ⟨5945935151306177272889305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31711654140299612122076293 5945935151306177272889305)
          ·
            refine ⟨4459451363479632954666979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945935151306177272889305 4459451363479632954666979)
            ·
              refine ⟨6689177045219449432000469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459451363479632954666979 6689177045219449432000469)
              ·
                refine ⟨156777586997330846062511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6689177045219449432000469 156777586997330846062511)
                ·
                  rfl

theorem cell22_4121864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_4121864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121864 prefixEnd_4121864 := by exact prefixLift 4121864
  have htrace : WordTrace (prefixWord ++ tailWord_4121864) baseStart_4121864 baseEnd_4121864 := by
    simpa [prefixWord, tailWord_4121864, baseEnd_4121864] using wordTrace_append hprefix tailTrace_4121864
  have hstable : (prefixWord ++ tailWord_4121864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121864).length < 2 ^ (prefixWord ++ tailWord_4121864).sum := by decide
  have hdescent : baseEnd_4121864 < baseStart_4121864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121875 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 11]
def baseStart_4121875 : Nat := 118140960795 + 4121875 * 2 ^ 59
def prefixEnd_4121875 : Nat := 4983230072969 + 3 ^ 40 * 4121875 * 2
def baseEnd_4121875 : Nat := 470334016166925750845855

theorem tailTrace_4121875 : CollatzResearch.WordTrace tailWord_4121875 prefixEnd_4121875 470334016166925750845855 := by
  unfold tailWord_4121875
  simp only [CollatzResearch.WordTrace]
  refine ⟨150337131942158310049975079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100224754628105540033316719 150337131942158310049975079)
  ·
    refine ⟨225505697913237465074962619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150337131942158310049975079 225505697913237465074962619)
    ·
      refine ⟨338258546869856197612443929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225505697913237465074962619 338258546869856197612443929)
      ·
        refine ⟨253693910152392148209332947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338258546869856197612443929 253693910152392148209332947)
        ·
          refine ⟨380540865228588222313999421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253693910152392148209332947 380540865228588222313999421)
          ·
            refine ⟨142702824460720583367749783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380540865228588222313999421 142702824460720583367749783)
            ·
              refine ⟨214054236691080875051624675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142702824460720583367749783 214054236691080875051624675)
              ·
                refine ⟨321081355036621312577437013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214054236691080875051624675 321081355036621312577437013)
                ·
                  refine ⟨470334016166925750845855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 321081355036621312577437013 470334016166925750845855)
                  ·
                    rfl

theorem cell22_4121875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_4121875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121875 prefixEnd_4121875 := by exact prefixLift 4121875
  have htrace : WordTrace (prefixWord ++ tailWord_4121875) baseStart_4121875 baseEnd_4121875 := by
    simpa [prefixWord, tailWord_4121875, baseEnd_4121875] using wordTrace_append hprefix tailTrace_4121875
  have hstable : (prefixWord ++ tailWord_4121875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121875).length < 2 ^ (prefixWord ++ tailWord_4121875).sum := by decide
  have hdescent : baseEnd_4121875 < baseStart_4121875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121879 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 3, 3]
def baseStart_4121879 : Nat := 118140960795 + 4121879 * 2 ^ 59
def prefixEnd_4121879 : Nat := 4983230072969 + 3 ^ 40 * 4121879 * 2
def baseEnd_4121879 : Nat := 1411003417782522575437553

theorem tailTrace_4121879 : CollatzResearch.WordTrace tailWord_4121879 prefixEnd_4121879 1411003417782522575437553 := by
  unfold tailWord_4121879
  simp only [CollatzResearch.WordTrace]
  refine ⟨150337277834143818733120691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100224851889429212488747127 150337277834143818733120691)
  ·
    refine ⟨225505916751215728099681037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150337277834143818733120691 225505916751215728099681037)
    ·
      refine ⟨84564718781705898037380389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225505916751215728099681037 84564718781705898037380389)
      ·
        refine ⟨15855884771569855882008823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84564718781705898037380389 15855884771569855882008823)
        ·
          refine ⟨23783827157354783823013235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855884771569855882008823 23783827157354783823013235)
          ·
            refine ⟨35675740736032175734519853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23783827157354783823013235 35675740736032175734519853)
            ·
              refine ⟨13378402776012065900444945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35675740736032175734519853 13378402776012065900444945)
              ·
                refine ⟨10033802082009049425333709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13378402776012065900444945 10033802082009049425333709)
                ·
                  refine ⟨3762675780753393534500141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10033802082009049425333709 3762675780753393534500141)
                  ·
                    refine ⟨1411003417782522575437553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762675780753393534500141 1411003417782522575437553)
                    ·
                      rfl

theorem cell22_4121879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_4121879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121879 prefixEnd_4121879 := by exact prefixLift 4121879
  have htrace : WordTrace (prefixWord ++ tailWord_4121879) baseStart_4121879 baseEnd_4121879 := by
    simpa [prefixWord, tailWord_4121879, baseEnd_4121879] using wordTrace_append hprefix tailTrace_4121879
  have hstable : (prefixWord ++ tailWord_4121879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121879).length < 2 ^ (prefixWord ++ tailWord_4121879).sum := by decide
  have hdescent : baseEnd_4121879 < baseStart_4121879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121892 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_4121892 : Nat := 118140960795 + 4121892 * 2 ^ 59
def prefixEnd_4121892 : Nat := 4983230072969 + 3 ^ 40 * 4121892 * 2
def baseEnd_4121892 : Nat := 470335955982731624954171

theorem tailTrace_4121892 : CollatzResearch.WordTrace tailWord_4121892 prefixEnd_4121892 470335955982731624954171 := by
  unfold tailWord_4121892
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168875991548360976671965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100225167988731147968895953 75168875991548360976671965)
  ·
    refine ⟨28188328496830635366251987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75168875991548360976671965 28188328496830635366251987)
    ·
      refine ⟨42282492745245953049377981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28188328496830635366251987 42282492745245953049377981)
      ·
        refine ⟨15855934779467232393516743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42282492745245953049377981 15855934779467232393516743)
        ·
          refine ⟨23783902169200848590275115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855934779467232393516743 23783902169200848590275115)
          ·
            refine ⟨35675853253801272885412673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23783902169200848590275115 35675853253801272885412673)
            ·
              refine ⟨26756889940350954664059505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35675853253801272885412673 26756889940350954664059505)
              ·
                refine ⟨20067667455263215998044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26756889940350954664059505 20067667455263215998044629)
                ·
                  refine ⟨470335955982731624954171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20067667455263215998044629 470335955982731624954171)
                  ·
                    rfl

theorem cell22_4121892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_4121892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121892 prefixEnd_4121892 := by exact prefixLift 4121892
  have htrace : WordTrace (prefixWord ++ tailWord_4121892) baseStart_4121892 baseEnd_4121892 := by
    simpa [prefixWord, tailWord_4121892, baseEnd_4121892] using wordTrace_append hprefix tailTrace_4121892
  have hstable : (prefixWord ++ tailWord_4121892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121892).length < 2 ^ (prefixWord ++ tailWord_4121892).sum := by decide
  have hdescent : baseEnd_4121892 < baseStart_4121892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121907 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_4121907 : Nat := 118140960795 + 4121907 * 2 ^ 59
def prefixEnd_4121907 : Nat := 4983230072969 + 3 ^ 40 * 4121907 * 2
def baseEnd_4121907 : Nat := 1411013002754739835737467

theorem tailTrace_4121907 : CollatzResearch.WordTrace tailWord_4121907 prefixEnd_4121907 1411013002754739835737467 := by
  unfold tailWord_4121907
  simp only [CollatzResearch.WordTrace]
  refine ⟨150338299078042379515139975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100225532718694919676759983 150338299078042379515139975)
  ·
    refine ⟨225507448617063569272709963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150338299078042379515139975 225507448617063569272709963)
    ·
      refine ⟨338261172925595353909064945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225507448617063569272709963 338261172925595353909064945)
      ·
        refine ⟨253695879694196515431798709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338261172925595353909064945 253695879694196515431798709)
        ·
          refine ⟨23783988721330923321731129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253695879694196515431798709 23783988721330923321731129)
          ·
            refine ⟨17837991540998192491298347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23783988721330923321731129 17837991540998192491298347)
            ·
              refine ⟨26756987311497288736947521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837991540998192491298347 26756987311497288736947521)
              ·
                refine ⟨20067740483622966552710641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26756987311497288736947521 20067740483622966552710641)
                ·
                  refine ⟨15050805362717224914532981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20067740483622966552710641 15050805362717224914532981)
                  ·
                    refine ⟨1411013002754739835737467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15050805362717224914532981 1411013002754739835737467)
                    ·
                      rfl

theorem cell22_4121907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_4121907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121907 prefixEnd_4121907 := by exact prefixLift 4121907
  have htrace : WordTrace (prefixWord ++ tailWord_4121907) baseStart_4121907 baseEnd_4121907 := by
    simpa [prefixWord, tailWord_4121907, baseEnd_4121907] using wordTrace_append hprefix tailTrace_4121907
  have hstable : (prefixWord ++ tailWord_4121907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121907).length < 2 ^ (prefixWord ++ tailWord_4121907).sum := by decide
  have hdescent : baseEnd_4121907 < baseStart_4121907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121909 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 5]
def baseStart_4121909 : Nat := 118140960795 + 4121909 * 2 ^ 59
def prefixEnd_4121909 : Nat := 4983230072969 + 3 ^ 40 * 4121909 * 2
def baseEnd_4121909 : Nat := 470337895798537499062487

theorem tailTrace_4121909 : CollatzResearch.WordTrace tailWord_4121909 prefixEnd_4121909 470337895798537499062487 := by
  unfold tailWord_4121909
  simp only [CollatzResearch.WordTrace]
  refine ⟨150338372024035133856712781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100225581349356755904475187 150338372024035133856712781)
  ·
    refine ⟨56376889509013175196267293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150338372024035133856712781 56376889509013175196267293)
    ·
      refine ⟨21141333565879940698600235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56376889509013175196267293 21141333565879940698600235)
      ·
        refine ⟨31712000348819911047900353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21141333565879940698600235 31712000348819911047900353)
        ·
          refine ⟨23784000261614933285925265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31712000348819911047900353 23784000261614933285925265)
          ·
            refine ⟨17838000196211199964443949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23784000261614933285925265 17838000196211199964443949)
            ·
              refine ⟨6689250073579199986666481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17838000196211199964443949 6689250073579199986666481)
              ·
                refine ⟨5016937555184399989999861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689250073579199986666481 5016937555184399989999861)
                ·
                  refine ⟨470337895798537499062487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016937555184399989999861 470337895798537499062487)
                  ·
                    rfl

theorem cell22_4121909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_4121909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121909 prefixEnd_4121909 := by exact prefixLift 4121909
  have htrace : WordTrace (prefixWord ++ tailWord_4121909) baseStart_4121909 baseEnd_4121909 := by
    simpa [prefixWord, tailWord_4121909, baseEnd_4121909] using wordTrace_append hprefix tailTrace_4121909
  have hstable : (prefixWord ++ tailWord_4121909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121909).length < 2 ^ (prefixWord ++ tailWord_4121909).sum := by decide
  have hdescent : baseEnd_4121909 < baseStart_4121909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121937 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 6]
def baseStart_4121937 : Nat := 118140960795 + 4121937 * 2 ^ 59
def prefixEnd_4121937 : Nat := 4983230072969 + 3 ^ 40 * 4121937 * 2
def baseEnd_4121937 : Nat := 470341090789276585829125

theorem tailTrace_4121937 : CollatzResearch.WordTrace tailWord_4121937 prefixEnd_4121937 470341090789276585829125 := by
  unfold tailWord_4121937
  simp only [CollatzResearch.WordTrace]
  refine ⟨150339393267933694638732065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100226262178622463092488043 150339393267933694638732065)
  ·
    refine ⟨112754544950950270979049049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150339393267933694638732065 112754544950950270979049049)
    ·
      refine ⟨84565908713212703234286787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112754544950950270979049049 84565908713212703234286787)
      ·
        refine ⟨126848863069819054851430181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84565908713212703234286787 126848863069819054851430181)
        ·
          refine ⟨23784161825591072784643159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126848863069819054851430181 23784161825591072784643159)
          ·
            refine ⟨35676242738386609176964739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23784161825591072784643159 35676242738386609176964739)
            ·
              refine ⟨53514364107579913765447109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35676242738386609176964739 53514364107579913765447109)
              ·
                refine ⟨10033943270171233831021333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53514364107579913765447109 10033943270171233831021333)
                ·
                  refine ⟨470341090789276585829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10033943270171233831021333 470341090789276585829125)
                  ·
                    rfl

theorem cell22_4121937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_4121937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121937 prefixEnd_4121937 := by exact prefixLift 4121937
  have htrace : WordTrace (prefixWord ++ tailWord_4121937) baseStart_4121937 baseEnd_4121937 := by
    simpa [prefixWord, tailWord_4121937, baseEnd_4121937] using wordTrace_append hprefix tailTrace_4121937
  have hstable : (prefixWord ++ tailWord_4121937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121937).length < 2 ^ (prefixWord ++ tailWord_4121937).sum := by decide
  have hdescent : baseEnd_4121937 < baseStart_4121937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121939 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 1, 4]
def baseStart_4121939 : Nat := 118140960795 + 4121939 * 2 ^ 59
def prefixEnd_4121939 : Nat := 4983230072969 + 3 ^ 40 * 4121939 * 2
def baseEnd_4121939 : Nat := 1411023957008702418937369

theorem tailTrace_4121939 : CollatzResearch.WordTrace tailWord_4121939 prefixEnd_4121939 1411023957008702418937369 := by
  unfold tailWord_4121939
  simp only [CollatzResearch.WordTrace]
  refine ⟨150339466213926448980304871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100226310809284299320203247 150339466213926448980304871)
  ·
    refine ⟨225509199320889673470457307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150339466213926448980304871 225509199320889673470457307)
    ·
      refine ⟨338263798981334510205685961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225509199320889673470457307 338263798981334510205685961)
      ·
        refine ⟨253697849236000882654264471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338263798981334510205685961 253697849236000882654264471)
        ·
          refine ⟨380546773854001323981396707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253697849236000882654264471 380546773854001323981396707)
          ·
            refine ⟨570820160781001985972095061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380546773854001323981396707 570820160781001985972095061)
            ·
              refine ⟨6689298759152367023110489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 570820160781001985972095061 6689298759152367023110489)
              ·
                refine ⟨5016974069364275267332867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689298759152367023110489 5016974069364275267332867)
                ·
                  refine ⟨7525461104046412900999301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016974069364275267332867 7525461104046412900999301)
                  ·
                    refine ⟨1411023957008702418937369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525461104046412900999301 1411023957008702418937369)
                    ·
                      rfl

theorem cell22_4121939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_4121939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121939 prefixEnd_4121939 := by exact prefixLift 4121939
  have htrace : WordTrace (prefixWord ++ tailWord_4121939) baseStart_4121939 baseEnd_4121939 := by
    simpa [prefixWord, tailWord_4121939, baseEnd_4121939] using wordTrace_append hprefix tailTrace_4121939
  have hstable : (prefixWord ++ tailWord_4121939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121939).length < 2 ^ (prefixWord ++ tailWord_4121939).sum := by decide
  have hdescent : baseEnd_4121939 < baseStart_4121939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4121969 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_4121969 : Nat := 118140960795 + 4121969 * 2 ^ 59
def prefixEnd_4121969 : Nat := 4983230072969 + 3 ^ 40 * 4121969 * 2
def baseEnd_4121969 : Nat := 1411034226621792340687277

theorem tailTrace_4121969 : CollatzResearch.WordTrace tailWord_4121969 prefixEnd_4121969 1411034226621792340687277 := by
  unfold tailWord_4121969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150340560403817764103896961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100227040269211842735931307 150340560403817764103896961)
  ·
    refine ⟨112755420302863323077922721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150340560403817764103896961 112755420302863323077922721)
    ·
      refine ⟨84566565227147492308442041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112755420302863323077922721 84566565227147492308442041)
      ·
        refine ⟨63424923920360619231331531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84566565227147492308442041 63424923920360619231331531)
        ·
          refine ⟨95137385880540928846997297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63424923920360619231331531 95137385880540928846997297)
          ·
            refine ⟨71353039410405696635247973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95137385880540928846997297 71353039410405696635247973)
            ·
              refine ⟨13378694889451068119108995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71353039410405696635247973 13378694889451068119108995)
              ·
                refine ⟨20068042334176602178663493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378694889451068119108995 20068042334176602178663493)
                ·
                  refine ⟨3762757937658112908499405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20068042334176602178663493 3762757937658112908499405)
                  ·
                    refine ⟨1411034226621792340687277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762757937658112908499405 1411034226621792340687277)
                    ·
                      rfl

theorem cell22_4121969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_4121969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4121969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4121969 prefixEnd_4121969 := by exact prefixLift 4121969
  have htrace : WordTrace (prefixWord ++ tailWord_4121969) baseStart_4121969 baseEnd_4121969 := by
    simpa [prefixWord, tailWord_4121969, baseEnd_4121969] using wordTrace_append hprefix tailTrace_4121969
  have hstable : (prefixWord ++ tailWord_4121969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4121969).length < 2 ^ (prefixWord ++ tailWord_4121969).sum := by decide
  have hdescent : baseEnd_4121969 < baseStart_4121969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4121969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122211 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_4122211 : Nat := 118140960795 + 4122211 * 2 ^ 59
def prefixEnd_4122211 : Nat := 4983230072969 + 3 ^ 40 * 4122211 * 2
def baseEnd_4122211 : Nat := 1411117068167384376136535

theorem tailTrace_4122211 : CollatzResearch.WordTrace tailWord_4122211 prefixEnd_4122211 1411117068167384376136535 := by
  unfold tailWord_4122211
  simp only [CollatzResearch.WordTrace]
  refine ⟨150349386868941039434206487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100232924579294026289470991 150349386868941039434206487)
  ·
    refine ⟨225524080303411559151309731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150349386868941039434206487 225524080303411559151309731)
    ·
      refine ⟨338286120455117338726964597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225524080303411559151309731 338286120455117338726964597)
      ·
        refine ⟨31714323792667250505652931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338286120455117338726964597 31714323792667250505652931)
        ·
          refine ⟨47571485689000875758479397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31714323792667250505652931 47571485689000875758479397)
          ·
            refine ⟨8919653566687664204714887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47571485689000875758479397 8919653566687664204714887)
            ·
              refine ⟨13379480350031496307072331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919653566687664204714887 13379480350031496307072331)
              ·
                refine ⟨20069220525047244460608497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379480350031496307072331 20069220525047244460608497)
                ·
                  refine ⟨15051915393785433345456373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20069220525047244460608497 15051915393785433345456373)
                  ·
                    refine ⟨1411117068167384376136535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15051915393785433345456373 1411117068167384376136535)
                    ·
                      rfl

theorem cell22_4122211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_4122211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122211 prefixEnd_4122211 := by exact prefixLift 4122211
  have htrace : WordTrace (prefixWord ++ tailWord_4122211) baseStart_4122211 baseEnd_4122211 := by
    simpa [prefixWord, tailWord_4122211, baseEnd_4122211] using wordTrace_append hprefix tailTrace_4122211
  have hstable : (prefixWord ++ tailWord_4122211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122211).length < 2 ^ (prefixWord ++ tailWord_4122211).sum := by decide
  have hdescent : baseEnd_4122211 < baseStart_4122211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_4122239 : Nat := 118140960795 + 4122239 * 2 ^ 59
def prefixEnd_4122239 : Nat := 4983230072969 + 3 ^ 40 * 4122239 * 2
def baseEnd_4122239 : Nat := 1411126653139601636436449

theorem tailTrace_4122239 : CollatzResearch.WordTrace tailWord_4122239 prefixEnd_4122239 1411126653139601636436449 := by
  unfold tailWord_4122239
  simp only [CollatzResearch.WordTrace]
  refine ⟨150350408112839600216225771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100233605408559733477483847 150350408112839600216225771)
  ·
    refine ⟨225525612169259400324338657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150350408112839600216225771 225525612169259400324338657)
    ·
      refine ⟨169144209126944550243253993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225525612169259400324338657 169144209126944550243253993)
      ·
        refine ⟨126858156845208412682440495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169144209126944550243253993 126858156845208412682440495)
        ·
          refine ⟨190287235267812619023660743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126858156845208412682440495 190287235267812619023660743)
          ·
            refine ⟨285430852901718928535491115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190287235267812619023660743 285430852901718928535491115)
            ·
              refine ⟨428146279352578392803236673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285430852901718928535491115 428146279352578392803236673)
              ·
                refine ⟨321109709514433794602427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428146279352578392803236673 321109709514433794602427505)
                ·
                  refine ⟨240832282135825345951820629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321109709514433794602427505 240832282135825345951820629)
                  ·
                    refine ⟨1411126653139601636436449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240832282135825345951820629 1411126653139601636436449)
                    ·
                      rfl

theorem cell22_4122239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_4122239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122239 prefixEnd_4122239 := by exact prefixLift 4122239
  have htrace : WordTrace (prefixWord ++ tailWord_4122239) baseStart_4122239 baseEnd_4122239 := by
    simpa [prefixWord, tailWord_4122239, baseEnd_4122239] using wordTrace_append hprefix tailTrace_4122239
  have hstable : (prefixWord ++ tailWord_4122239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122239).length < 2 ^ (prefixWord ++ tailWord_4122239).sum := by decide
  have hdescent : baseEnd_4122239 < baseStart_4122239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122273 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4122273 : Nat := 118140960795 + 4122273 * 2 ^ 59
def prefixEnd_4122273 : Nat := 4983230072969 + 3 ^ 40 * 4122273 * 2
def baseEnd_4122273 : Nat := 1411138292034436881086345

theorem tailTrace_4122273 : CollatzResearch.WordTrace tailWord_4122273 prefixEnd_4122273 1411138292034436881086345 := by
  unfold tailWord_4122273
  simp only [CollatzResearch.WordTrace]
  refine ⟨150351648194716424022963473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100234432129810949348642315 150351648194716424022963473)
  ·
    refine ⟨112763736146037318017222605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150351648194716424022963473 112763736146037318017222605)
    ·
      refine ⟨42286401054763994256458477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112763736146037318017222605 42286401054763994256458477)
      ·
        refine ⟨15857400395536497846171929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42286401054763994256458477 15857400395536497846171929)
        ·
          refine ⟨11893050296652373384628947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15857400395536497846171929 11893050296652373384628947)
          ·
            refine ⟨17839575444978560076943421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893050296652373384628947 17839575444978560076943421)
            ·
              refine ⟨6689840791866960028853783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17839575444978560076943421 6689840791866960028853783)
              ·
                refine ⟨10034761187800440043280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689840791866960028853783 10034761187800440043280675)
                ·
                  refine ⟨15052141781700660064921013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10034761187800440043280675 15052141781700660064921013)
                  ·
                    refine ⟨1411138292034436881086345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15052141781700660064921013 1411138292034436881086345)
                    ·
                      rfl

theorem cell22_4122273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4122273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122273 prefixEnd_4122273 := by exact prefixLift 4122273
  have htrace : WordTrace (prefixWord ++ tailWord_4122273) baseStart_4122273 baseEnd_4122273 := by
    simpa [prefixWord, tailWord_4122273, baseEnd_4122273] using wordTrace_append hprefix tailTrace_4122273
  have hstable : (prefixWord ++ tailWord_4122273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122273).length < 2 ^ (prefixWord ++ tailWord_4122273).sum := by decide
  have hdescent : baseEnd_4122273 < baseStart_4122273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122324 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_4122324 : Nat := 118140960795 + 4122324 * 2 ^ 59
def prefixEnd_4122324 : Nat := 4983230072969 + 3 ^ 40 * 4122324 * 2
def baseEnd_4122324 : Nat := 1411155750376689748061189

theorem tailTrace_4122324 : CollatzResearch.WordTrace tailWord_4122324 prefixEnd_4122324 1411155750376689748061189 := by
  unfold tailWord_4122324
  simp only [CollatzResearch.WordTrace]
  refine ⟨75176754158765829866535013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100235672211687773155380017 75176754158765829866535013)
  ·
    refine ⟨14095641404768593099975315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75176754158765829866535013 14095641404768593099975315)
    ·
      refine ⟨21143462107152889649962973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14095641404768593099975315 21143462107152889649962973)
      ·
        refine ⟨7928798290182333618736115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21143462107152889649962973 7928798290182333618736115)
        ·
          refine ⟨11893197435273500428104173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928798290182333618736115 11893197435273500428104173)
          ·
            refine ⟨4459949038227562660539065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11893197435273500428104173 4459949038227562660539065)
            ·
              refine ⟨3344961778670671995404299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459949038227562660539065 3344961778670671995404299)
              ·
                refine ⟨5017442668006007993106449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344961778670671995404299 5017442668006007993106449)
                ·
                  refine ⟨3763082001004505994829837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017442668006007993106449 3763082001004505994829837)
                  ·
                    refine ⟨1411155750376689748061189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763082001004505994829837 1411155750376689748061189)
                    ·
                      rfl

theorem cell22_4122324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_4122324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122324 prefixEnd_4122324 := by exact prefixLift 4122324
  have htrace : WordTrace (prefixWord ++ tailWord_4122324) baseStart_4122324 baseEnd_4122324 := by
    simpa [prefixWord, tailWord_4122324, baseEnd_4122324] using wordTrace_append hprefix tailTrace_4122324
  have hstable : (prefixWord ++ tailWord_4122324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122324).length < 2 ^ (prefixWord ++ tailWord_4122324).sum := by decide
  have hdescent : baseEnd_4122324 < baseStart_4122324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122378 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_4122378 : Nat := 118140960795 + 4122378 * 2 ^ 59
def prefixEnd_4122378 : Nat := 4983230072969 + 3 ^ 40 * 4122378 * 2
def baseEnd_4122378 : Nat := 1411174235680251607211023

theorem tailTrace_4122378 : CollatzResearch.WordTrace tailWord_4122378 prefixEnd_4122378 1411174235680251607211023 := by
  unfold tailWord_4122378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588869464834006738883947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100236985239557351303690525 37588869464834006738883947)
  ·
    refine ⟨56383304197251010108325921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37588869464834006738883947 56383304197251010108325921)
    ·
      refine ⟨42287478147938257581244441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56383304197251010108325921 42287478147938257581244441)
      ·
        refine ⟨31715608610953693185933331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42287478147938257581244441 31715608610953693185933331)
        ·
          refine ⟨47573412916430539778899997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31715608610953693185933331 47573412916430539778899997)
          ·
            refine ⟨17840029843661452417087499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47573412916430539778899997 17840029843661452417087499)
            ·
              refine ⟨26760044765492178625631249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17840029843661452417087499 26760044765492178625631249)
              ·
                refine ⟨20070033574119133969223437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26760044765492178625631249 20070033574119133969223437)
                ·
                  refine ⟨7526262590294675238458789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20070033574119133969223437 7526262590294675238458789)
                  ·
                    refine ⟨1411174235680251607211023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526262590294675238458789 1411174235680251607211023)
                    ·
                      rfl

theorem cell22_4122378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_4122378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122378 prefixEnd_4122378 := by exact prefixLift 4122378
  have htrace : WordTrace (prefixWord ++ tailWord_4122378) baseStart_4122378 baseEnd_4122378 := by
    simpa [prefixWord, tailWord_4122378, baseEnd_4122378] using wordTrace_append hprefix tailTrace_4122378
  have hstable : (prefixWord ++ tailWord_4122378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122378).length < 2 ^ (prefixWord ++ tailWord_4122378).sum := by decide
  have hdescent : baseEnd_4122378 < baseStart_4122378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122412 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_4122412 : Nat := 118140960795 + 4122412 * 2 ^ 59
def prefixEnd_4122412 : Nat := 4983230072969 + 3 ^ 40 * 4122412 * 2
def baseEnd_4122412 : Nat := 1411185874575086851860919

theorem tailTrace_4122412 : CollatzResearch.WordTrace tailWord_4122412 prefixEnd_4122412 1411185874575086851860919 := by
  unfold tailWord_4122412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75178358970606425381136745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100237811960808567174848993 75178358970606425381136745)
  ·
    refine ⟨56383769227954819035852559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75178358970606425381136745 56383769227954819035852559)
    ·
      refine ⟨84575653841932228553778839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56383769227954819035852559 84575653841932228553778839)
      ·
        refine ⟨126863480762898342830668259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84575653841932228553778839 126863480762898342830668259)
        ·
          refine ⟨190295221144347514246002389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126863480762898342830668259 190295221144347514246002389)
          ·
            refine ⟨4460044245570644865140681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190295221144347514246002389 4460044245570644865140681)
            ·
              refine ⟨3345033184177983648855511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460044245570644865140681 3345033184177983648855511)
              ·
                refine ⟨5017549776266975473283267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345033184177983648855511 5017549776266975473283267)
                ·
                  refine ⟨7526324664400463209924901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017549776266975473283267 7526324664400463209924901)
                  ·
                    refine ⟨1411185874575086851860919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526324664400463209924901 1411185874575086851860919)
                    ·
                      rfl

theorem cell22_4122412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_4122412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122412 prefixEnd_4122412 := by exact prefixLift 4122412
  have htrace : WordTrace (prefixWord ++ tailWord_4122412) baseStart_4122412 baseEnd_4122412 := by
    simpa [prefixWord, tailWord_4122412, baseEnd_4122412] using wordTrace_append hprefix tailTrace_4122412
  have hstable : (prefixWord ++ tailWord_4122412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122412).length < 2 ^ (prefixWord ++ tailWord_4122412).sum := by decide
  have hdescent : baseEnd_4122412 < baseStart_4122412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122442 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_4122442 : Nat := 118140960795 + 4122442 * 2 ^ 59
def prefixEnd_4122442 : Nat := 4983230072969 + 3 ^ 40 * 4122442 * 2
def baseEnd_4122442 : Nat := 1411196144188176773610827

theorem tailTrace_4122442 : CollatzResearch.WordTrace tailWord_4122442 prefixEnd_4122442 1411196144188176773610827 := by
  unfold tailWord_4122442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37589453032776041471466395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100238541420736110590577053 37589453032776041471466395)
  ·
    refine ⟨56384179549164062207199593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37589453032776041471466395 56384179549164062207199593)
    ·
      refine ⟨42288134661873046655399695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56384179549164062207199593 42288134661873046655399695)
      ·
        refine ⟨63432201992809569983099543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42288134661873046655399695 63432201992809569983099543)
        ·
          refine ⟨95148302989214354974649315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63432201992809569983099543 95148302989214354974649315)
          ·
            refine ⟨142722454483821532461973973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95148302989214354974649315 142722454483821532461973973)
            ·
              refine ⟨3345057526964567167077515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142722454483821532461973973 3345057526964567167077515)
              ·
                refine ⟨5017586290446850750616273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345057526964567167077515 5017586290446850750616273)
                ·
                  refine ⟨3763189717835138062962205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017586290446850750616273 3763189717835138062962205)
                  ·
                    refine ⟨1411196144188176773610827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763189717835138062962205 1411196144188176773610827)
                    ·
                      rfl

theorem cell22_4122442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_4122442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122442 prefixEnd_4122442 := by exact prefixLift 4122442
  have htrace : WordTrace (prefixWord ++ tailWord_4122442) baseStart_4122442 baseEnd_4122442 := by
    simpa [prefixWord, tailWord_4122442, baseEnd_4122442] using wordTrace_append hprefix tailTrace_4122442
  have hstable : (prefixWord ++ tailWord_4122442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122442).length < 2 ^ (prefixWord ++ tailWord_4122442).sum := by decide
  have hdescent : baseEnd_4122442 < baseStart_4122442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122483 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 5]
def baseStart_4122483 : Nat := 118140960795 + 4122483 * 2 ^ 59
def prefixEnd_4122483 : Nat := 4983230072969 + 3 ^ 40 * 4122483 * 2
def baseEnd_4122483 : Nat := 470403393108688777778567

theorem tailTrace_4122483 : CollatzResearch.WordTrace tailWord_4122483 prefixEnd_4122483 470403393108688777778567 := by
  unfold tailWord_4122483
  simp only [CollatzResearch.WordTrace]
  refine ⟨150359307523955629888108103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100239538349303753258738735 150359307523955629888108103)
  ·
    refine ⟨225538961285933444832162155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150359307523955629888108103 225538961285933444832162155)
    ·
      refine ⟨338308441928900167248243233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225538961285933444832162155 338308441928900167248243233)
      ·
        refine ⟨253731331446675125436182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338308441928900167248243233 253731331446675125436182425)
        ·
          refine ⟨190298498585006344077136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253731331446675125436182425 190298498585006344077136819)
          ·
            refine ⟨285447747877509516115705229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190298498585006344077136819 285447747877509516115705229)
            ·
              refine ⟨107042905454066068543389461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285447747877509516115705229 107042905454066068543389461)
              ·
                refine ⟨5017636193159346962971381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107042905454066068543389461 5017636193159346962971381)
                ·
                  refine ⟨470403393108688777778567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017636193159346962971381 470403393108688777778567)
                  ·
                    rfl

theorem cell22_4122483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].length) (baseStart_4122483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122483 prefixEnd_4122483 := by exact prefixLift 4122483
  have htrace : WordTrace (prefixWord ++ tailWord_4122483) baseStart_4122483 baseEnd_4122483 := by
    simpa [prefixWord, tailWord_4122483, baseEnd_4122483] using wordTrace_append hprefix tailTrace_4122483
  have hstable : (prefixWord ++ tailWord_4122483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122483).length < 2 ^ (prefixWord ++ tailWord_4122483).sum := by decide
  have hdescent : baseEnd_4122483 < baseStart_4122483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122543 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_4122543 : Nat := 118140960795 + 4122543 * 2 ^ 59
def prefixEnd_4122543 : Nat := 4983230072969 + 3 ^ 40 * 4122543 * 2
def baseEnd_4122543 : Nat := 1411230718552246176835517

theorem tailTrace_4122543 : CollatzResearch.WordTrace tailWord_4122543 prefixEnd_4122543 1411230718552246176835517 := by
  unfold tailWord_4122543
  simp only [CollatzResearch.WordTrace]
  refine ⟨150361495903738260135292283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100240997269158840090194855 150361495903738260135292283)
  ·
    refine ⟨225542243855607390202938425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150361495903738260135292283 225542243855607390202938425)
    ·
      refine ⟨169156682891705542652203819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225542243855607390202938425 169156682891705542652203819)
      ·
        refine ⟨253735024337558313978305729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169156682891705542652203819 253735024337558313978305729)
        ·
          refine ⟨190301268253168735483729297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253735024337558313978305729 190301268253168735483729297)
          ·
            refine ⟨142725951189876551612796973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190301268253168735483729297 142725951189876551612796973)
            ·
              refine ⟨53522231696203706854798865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142725951189876551612796973 53522231696203706854798865)
              ·
                refine ⟨40141673772152780141099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53522231696203706854798865 40141673772152780141099149)
                ·
                  refine ⟨15053127664557292552912181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40141673772152780141099149 15053127664557292552912181)
                  ·
                    refine ⟨1411230718552246176835517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15053127664557292552912181 1411230718552246176835517)
                    ·
                      rfl

theorem cell22_4122543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_4122543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122543 prefixEnd_4122543 := by exact prefixLift 4122543
  have htrace : WordTrace (prefixWord ++ tailWord_4122543) baseStart_4122543 baseEnd_4122543 := by
    simpa [prefixWord, tailWord_4122543, baseEnd_4122543] using wordTrace_append hprefix tailTrace_4122543
  have hstable : (prefixWord ++ tailWord_4122543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122543).length < 2 ^ (prefixWord ++ tailWord_4122543).sum := by decide
  have hdescent : baseEnd_4122543 < baseStart_4122543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122560 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_4122560 : Nat := 118140960795 + 4122560 * 2 ^ 59
def prefixEnd_4122560 : Nat := 4983230072969 + 3 ^ 40 * 4122560 * 2
def baseEnd_4122560 : Nat := 1411236537999663799160465

theorem tailTrace_4122560 : CollatzResearch.WordTrace tailWord_4122560 prefixEnd_4122560 1411236537999663799160465 := by
  unfold tailWord_4122560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75181057972338336019330567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100241410629784448025774089 75181057972338336019330567)
  ·
    refine ⟨112771586958507504028995851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75181057972338336019330567 112771586958507504028995851)
    ·
      refine ⟨169157380437761256043493777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112771586958507504028995851 169157380437761256043493777)
      ·
        refine ⟨126868035328320942032620333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169157380437761256043493777 126868035328320942032620333)
        ·
          refine ⟨47575513248120353262232625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126868035328320942032620333 47575513248120353262232625)
          ·
            refine ⟨35681634936090264946674469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47575513248120353262232625 35681634936090264946674469)
            ·
              refine ⟨6690306550516924677501463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35681634936090264946674469 6690306550516924677501463)
              ·
                refine ⟨10035459825775387016252195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690306550516924677501463 10035459825775387016252195)
                ·
                  refine ⟨15053189738663080524378293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10035459825775387016252195 15053189738663080524378293)
                  ·
                    refine ⟨1411236537999663799160465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15053189738663080524378293 1411236537999663799160465)
                    ·
                      rfl

theorem cell22_4122560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_4122560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122560 prefixEnd_4122560 := by exact prefixLift 4122560
  have htrace : WordTrace (prefixWord ++ tailWord_4122560) baseStart_4122560 baseEnd_4122560 := by
    simpa [prefixWord, tailWord_4122560, baseEnd_4122560] using wordTrace_append hprefix tailTrace_4122560
  have hstable : (prefixWord ++ tailWord_4122560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122560).length < 2 ^ (prefixWord ++ tailWord_4122560).sum := by decide
  have hdescent : baseEnd_4122560 < baseStart_4122560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122603 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_4122603 : Nat := 118140960795 + 4122603 * 2 ^ 59
def prefixEnd_4122603 : Nat := 4983230072969 + 3 ^ 40 * 4122603 * 2
def baseEnd_4122603 : Nat := 1411251257778426020335333

theorem tailTrace_4122603 : CollatzResearch.WordTrace tailWord_4122603 prefixEnd_4122603 1411251257778426020335333 := by
  unfold tailWord_4122603
  simp only [CollatzResearch.WordTrace]
  refine ⟨150363684283520890382476463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100242456189013926921650975 150363684283520890382476463)
  ·
    refine ⟨225545526425281335573714695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150363684283520890382476463 225545526425281335573714695)
    ·
      refine ⟨338318289637922003360572043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225545526425281335573714695 338318289637922003360572043)
      ·
        refine ⟨507477434456883005040858065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338318289637922003360572043 507477434456883005040858065)
        ·
          refine ⟨380608075842662253780643549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507477434456883005040858065 380608075842662253780643549)
          ·
            refine ⟨142728028440998345167741331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380608075842662253780643549 142728028440998345167741331)
            ·
              refine ⟨214092042661497517751611997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142728028440998345167741331 214092042661497517751611997)
              ·
                refine ⟨80284515998061569156854499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214092042661497517751611997 80284515998061569156854499)
                ·
                  refine ⟨120426773997092353735281749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80284515998061569156854499 120426773997092353735281749)
                  ·
                    refine ⟨1411251257778426020335333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120426773997092353735281749 1411251257778426020335333)
                    ·
                      rfl

theorem cell22_4122603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_4122603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122603 prefixEnd_4122603 := by exact prefixLift 4122603
  have htrace : WordTrace (prefixWord ++ tailWord_4122603) baseStart_4122603 baseEnd_4122603 := by
    simpa [prefixWord, tailWord_4122603, baseEnd_4122603] using wordTrace_append hprefix tailTrace_4122603
  have hstable : (prefixWord ++ tailWord_4122603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122603).length < 2 ^ (prefixWord ++ tailWord_4122603).sum := by decide
  have hdescent : baseEnd_4122603 < baseStart_4122603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122697 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 4]
def baseStart_4122697 : Nat := 118140960795 + 4122697 * 2 ^ 59
def prefixEnd_4122697 : Nat := 4983230072969 + 3 ^ 40 * 4122697 * 2
def baseEnd_4122697 : Nat := 470427811966480369495015

theorem tailTrace_4122697 : CollatzResearch.WordTrace tailWord_4122697 prefixEnd_4122697 470427811966480369495015 := by
  unfold tailWord_4122697
  simp only [CollatzResearch.WordTrace]
  refine ⟨150367112745180344436398345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100244741830120229624265563 150367112745180344436398345)
  ·
    refine ⟨112775334558885258327298759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150367112745180344436398345 112775334558885258327298759)
    ·
      refine ⟨169163001838327887490948139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112775334558885258327298759 169163001838327887490948139)
      ·
        refine ⟨253744502757491831236422209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169163001838327887490948139 253744502757491831236422209)
        ·
          refine ⟨190308377068118873427316657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253744502757491831236422209 190308377068118873427316657)
          ·
            refine ⟨142731282801089155070487493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190308377068118873427316657 142731282801089155070487493)
            ·
              refine ⟨26762115525204216575716405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142731282801089155070487493 26762115525204216575716405)
              ·
                refine ⟨2508948330487895303973413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26762115525204216575716405 2508948330487895303973413)
                ·
                  refine ⟨470427811966480369495015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508948330487895303973413 470427811966480369495015)
                  ·
                    rfl

theorem cell22_4122697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_4122697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122697 prefixEnd_4122697 := by exact prefixLift 4122697
  have htrace : WordTrace (prefixWord ++ tailWord_4122697) baseStart_4122697 baseEnd_4122697 := by
    simpa [prefixWord, tailWord_4122697, baseEnd_4122697] using wordTrace_append hprefix tailTrace_4122697
  have hstable : (prefixWord ++ tailWord_4122697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122697).length < 2 ^ (prefixWord ++ tailWord_4122697).sum := by decide
  have hdescent : baseEnd_4122697 < baseStart_4122697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122838 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4122838 : Nat := 118140960795 + 4122838 * 2 ^ 59
def prefixEnd_4122838 : Nat := 4983230072969 + 3 ^ 40 * 4122838 * 2
def baseEnd_4122838 : Nat := 470443901026987913569871

theorem tailTrace_4122838 : CollatzResearch.WordTrace tailWord_4122838 prefixEnd_4122838 470443901026987913569871 := by
  unfold tailWord_4122838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398265964854345344830073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100248170291779683678187445 9398265964854345344830073)
  ·
    refine ⟨7048699473640759008622555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9398265964854345344830073 7048699473640759008622555)
    ·
      refine ⟨10573049210461138512933833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048699473640759008622555 10573049210461138512933833)
      ·
        refine ⟨7929786907845853884700375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573049210461138512933833 7929786907845853884700375)
        ·
          refine ⟨11894680361768780827050563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929786907845853884700375 11894680361768780827050563)
          ·
            refine ⟨17842020542653171240575845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894680361768780827050563 17842020542653171240575845)
            ·
              refine ⟨3345378851747469607607971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17842020542653171240575845 3345378851747469607607971)
              ·
                refine ⟨5018068277621204411411957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345378851747469607607971 5018068277621204411411957)
                ·
                  refine ⟨470443901026987913569871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5018068277621204411411957 470443901026987913569871)
                  ·
                    rfl

theorem cell22_4122838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4122838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122838 prefixEnd_4122838 := by exact prefixLift 4122838
  have htrace : WordTrace (prefixWord ++ tailWord_4122838) baseStart_4122838 baseEnd_4122838 := by
    simpa [prefixWord, tailWord_4122838, baseEnd_4122838] using wordTrace_append hprefix tailTrace_4122838
  have hstable : (prefixWord ++ tailWord_4122838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122838).length < 2 ^ (prefixWord ++ tailWord_4122838).sum := by decide
  have hdescent : baseEnd_4122838 < baseStart_4122838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122847 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_4122847 : Nat := 118140960795 + 4122847 * 2 ^ 59
def prefixEnd_4122847 : Nat := 4983230072969 + 3 ^ 40 * 4122847 * 2
def baseEnd_4122847 : Nat := 1411334783964890717234585

theorem tailTrace_4122847 : CollatzResearch.WordTrace tailWord_4122847 prefixEnd_4122847 1411334783964890717234585 := by
  unfold tailWord_4122847
  simp only [CollatzResearch.WordTrace]
  refine ⟨150372583694636920054358795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100248389129757946702905863 150372583694636920054358795)
  ·
    refine ⟨225558875541955380081538193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150372583694636920054358795 225558875541955380081538193)
    ·
      refine ⟨169169156656466535061153645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225558875541955380081538193 169169156656466535061153645)
      ·
        refine ⟨63438433746174950647932617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169169156656466535061153645 63438433746174950647932617)
        ·
          refine ⟨47578825309631212985949463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63438433746174950647932617 47578825309631212985949463)
          ·
            refine ⟨71368237964446819478924195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47578825309631212985949463 71368237964446819478924195)
            ·
              refine ⟨107052356946670229218386293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71368237964446819478924195 107052356946670229218386293)
              ·
                refine ⟨10036158463750333989223715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107052356946670229218386293 10036158463750333989223715)
                ·
                  refine ⟨15054237695625500983835573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036158463750333989223715 15054237695625500983835573)
                  ·
                    refine ⟨1411334783964890717234585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15054237695625500983835573 1411334783964890717234585)
                    ·
                      rfl

theorem cell22_4122847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_4122847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122847 prefixEnd_4122847 := by exact prefixLift 4122847
  have htrace : WordTrace (prefixWord ++ tailWord_4122847) baseStart_4122847 baseEnd_4122847 := by
    simpa [prefixWord, tailWord_4122847, baseEnd_4122847] using wordTrace_append hprefix tailTrace_4122847
  have hstable : (prefixWord ++ tailWord_4122847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122847).length < 2 ^ (prefixWord ++ tailWord_4122847).sum := by decide
  have hdescent : baseEnd_4122847 < baseStart_4122847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122851 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 3, 4]
def baseStart_4122851 : Nat := 118140960795 + 4122851 * 2 ^ 59
def prefixEnd_4122851 : Nat := 4983230072969 + 3 ^ 40 * 4122851 * 2
def baseEnd_4122851 : Nat := 1411336153246636040134573

theorem tailTrace_4122851 : CollatzResearch.WordTrace tailWord_4122851 prefixEnd_4122851 1411336153246636040134573 := by
  unfold tailWord_4122851
  simp only [CollatzResearch.WordTrace]
  refine ⟨150372729586622428737504407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100248486391081619158336271 150372729586622428737504407)
  ·
    refine ⟨225559094379933643106256611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150372729586622428737504407 225559094379933643106256611)
    ·
      refine ⟨338338641569900464659384917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225559094379933643106256611 338338641569900464659384917)
      ·
        refine ⟨3964905955897271070227167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 338338641569900464659384917 3964905955897271070227167)
        ·
          refine ⟨5947358933845906605340751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964905955897271070227167 5947358933845906605340751)
          ·
            refine ⟨8921038400768859908011127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947358933845906605340751 8921038400768859908011127)
            ·
              refine ⟨13381557601153289862016691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921038400768859908011127 13381557601153289862016691)
              ·
                refine ⟨20072336401729934793025037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381557601153289862016691 20072336401729934793025037)
                ·
                  refine ⟨7527126150648725547384389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20072336401729934793025037 7527126150648725547384389)
                  ·
                    refine ⟨1411336153246636040134573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7527126150648725547384389 1411336153246636040134573)
                    ·
                      rfl

theorem cell22_4122851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].length) (baseStart_4122851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122851 prefixEnd_4122851 := by exact prefixLift 4122851
  have htrace : WordTrace (prefixWord ++ tailWord_4122851) baseStart_4122851 baseEnd_4122851 := by
    simpa [prefixWord, tailWord_4122851, baseEnd_4122851] using wordTrace_append hprefix tailTrace_4122851
  have hstable : (prefixWord ++ tailWord_4122851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122851).length < 2 ^ (prefixWord ++ tailWord_4122851).sum := by decide
  have hdescent : baseEnd_4122851 < baseStart_4122851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122881 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4122881 : Nat := 118140960795 + 4122881 * 2 ^ 59
def prefixEnd_4122881 : Nat := 4983230072969 + 3 ^ 40 * 4122881 * 2
def baseEnd_4122881 : Nat := 1411346422859725961884481

theorem tailTrace_4122881 : CollatzResearch.WordTrace tailWord_4122881 prefixEnd_4122881 1411346422859725961884481 := by
  unfold tailWord_4122881
  simp only [CollatzResearch.WordTrace]
  refine ⟨150373823776513743861096497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100249215851009162574064331 150373823776513743861096497)
  ·
    refine ⟨112780367832385307895822373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150373823776513743861096497 112780367832385307895822373)
    ·
      refine ⟨21146318968572245230466695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112780367832385307895822373 21146318968572245230466695)
      ·
        refine ⟨31719478452858367845700043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21146318968572245230466695 31719478452858367845700043)
        ·
          refine ⟨47579217679287551768550065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31719478452858367845700043 47579217679287551768550065)
          ·
            refine ⟨35684413259465663826412549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47579217679287551768550065 35684413259465663826412549)
            ·
              refine ⟨6690827486149811967452353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35684413259465663826412549 6690827486149811967452353)
              ·
                refine ⟨5018120614612358975589265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6690827486149811967452353 5018120614612358975589265)
                ·
                  refine ⟨3763590460959269231691949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5018120614612358975589265 3763590460959269231691949)
                  ·
                    refine ⟨1411346422859725961884481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763590460959269231691949 1411346422859725961884481)
                    ·
                      rfl

theorem cell22_4122881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4122881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122881 prefixEnd_4122881 := by exact prefixLift 4122881
  have htrace : WordTrace (prefixWord ++ tailWord_4122881) baseStart_4122881 baseEnd_4122881 := by
    simpa [prefixWord, tailWord_4122881, baseEnd_4122881] using wordTrace_append hprefix tailTrace_4122881
  have hstable : (prefixWord ++ tailWord_4122881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122881).length < 2 ^ (prefixWord ++ tailWord_4122881).sum := by decide
  have hdescent : baseEnd_4122881 < baseStart_4122881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122919 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4122919 : Nat := 118140960795 + 4122919 * 2 ^ 59
def prefixEnd_4122919 : Nat := 4983230072969 + 3 ^ 40 * 4122919 * 2
def baseEnd_4122919 : Nat := 1411359431036306529434365

theorem tailTrace_4122919 : CollatzResearch.WordTrace tailWord_4122919 prefixEnd_4122919 1411359431036306529434365 := by
  unfold tailWord_4122919
  simp only [CollatzResearch.WordTrace]
  refine ⟨150375209750376076350979811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100250139833584050900653207 150375209750376076350979811)
  ·
    refine ⟨225562814625564114526469717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150375209750376076350979811 225562814625564114526469717)
    ·
      refine ⟨2643314233893329467107067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 225562814625564114526469717 2643314233893329467107067)
      ·
        refine ⟨3964971350839994200660601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643314233893329467107067 3964971350839994200660601)
        ·
          refine ⟨2973728513129995650495451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964971350839994200660601 2973728513129995650495451)
          ·
            refine ⟨4460592769694993475743177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973728513129995650495451 4460592769694993475743177)
            ·
              refine ⟨3345444577271245106807383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460592769694993475743177 3345444577271245106807383)
              ·
                refine ⟨5018166865906867660211075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345444577271245106807383 5018166865906867660211075)
                ·
                  refine ⟨7527250298860301490316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018166865906867660211075 7527250298860301490316613)
                  ·
                    refine ⟨1411359431036306529434365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7527250298860301490316613 1411359431036306529434365)
                    ·
                      rfl

theorem cell22_4122919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4122919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122919 prefixEnd_4122919 := by exact prefixLift 4122919
  have htrace : WordTrace (prefixWord ++ tailWord_4122919) baseStart_4122919 baseEnd_4122919 := by
    simpa [prefixWord, tailWord_4122919, baseEnd_4122919] using wordTrace_append hprefix tailTrace_4122919
  have hstable : (prefixWord ++ tailWord_4122919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122919).length < 2 ^ (prefixWord ++ tailWord_4122919).sum := by decide
  have hdescent : baseEnd_4122919 < baseStart_4122919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4122956 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_4122956 : Nat := 118140960795 + 4122956 * 2 ^ 59
def prefixEnd_4122956 : Nat := 4983230072969 + 3 ^ 40 * 4122956 * 2
def baseEnd_4122956 : Nat := 470457365630816922086417

theorem tailTrace_4122956 : CollatzResearch.WordTrace tailWord_4122956 prefixEnd_4122956 470457365630816922086417 := by
  unfold tailWord_4122956
  simp only [CollatzResearch.WordTrace]
  refine ⟨75188279625621015835038361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100251039500828021113384481 75188279625621015835038361)
  ·
    refine ⟨56391209719215761876278771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75188279625621015835038361 56391209719215761876278771)
    ·
      refine ⟨84586814578823642814418157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56391209719215761876278771 84586814578823642814418157)
      ·
        refine ⟨31720055467058866055406809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84586814578823642814418157 31720055467058866055406809)
        ·
          refine ⟨23790041600294149541555107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31720055467058866055406809 23790041600294149541555107)
          ·
            refine ⟨35685062400441224312332661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790041600294149541555107 35685062400441224312332661)
            ·
              refine ⟨3345474600041364779281187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35685062400441224312332661 3345474600041364779281187)
              ·
                refine ⟨5018211900062047168921781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345474600041364779281187 5018211900062047168921781)
                ·
                  refine ⟨470457365630816922086417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5018211900062047168921781 470457365630816922086417)
                  ·
                    rfl

theorem cell22_4122956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_4122956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4122956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4122956 prefixEnd_4122956 := by exact prefixLift 4122956
  have htrace : WordTrace (prefixWord ++ tailWord_4122956) baseStart_4122956 baseEnd_4122956 := by
    simpa [prefixWord, tailWord_4122956, baseEnd_4122956] using wordTrace_append hprefix tailTrace_4122956
  have hstable : (prefixWord ++ tailWord_4122956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4122956).length < 2 ^ (prefixWord ++ tailWord_4122956).sum := by decide
  have hdescent : baseEnd_4122956 < baseStart_4122956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4122956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123048 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4123048 : Nat := 118140960795 + 4123048 * 2 ^ 59
def prefixEnd_4123048 : Nat := 4983230072969 + 3 ^ 40 * 4123048 * 2
def baseEnd_4123048 : Nat := 1411403590372593192958969

theorem tailTrace_4123048 : CollatzResearch.WordTrace tailWord_4123048 prefixEnd_4123048 1411403590372593192958969 := by
  unfold tailWord_4123048
  simp only [CollatzResearch.WordTrace]
  refine ⟨75189957383454365691212899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100253276511272487588283865 75189957383454365691212899)
  ·
    refine ⟨112784936075181548536819349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75189957383454365691212899 112784936075181548536819349)
    ·
      refine ⟨5286793878524135087663407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112784936075181548536819349 5286793878524135087663407)
      ·
        refine ⟨7930190817786202631495111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286793878524135087663407 7930190817786202631495111)
        ·
          refine ⟨11895286226679303947242667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930190817786202631495111 11895286226679303947242667)
          ·
            refine ⟨17842929340018955920864001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895286226679303947242667 17842929340018955920864001)
            ·
              refine ⟨13382197005014216940648001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17842929340018955920864001 13382197005014216940648001)
              ·
                refine ⟨10036647753760662705486001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382197005014216940648001 10036647753760662705486001)
                ·
                  refine ⟨7527485815320497029114501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10036647753760662705486001 7527485815320497029114501)
                  ·
                    refine ⟨1411403590372593192958969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7527485815320497029114501 1411403590372593192958969)
                    ·
                      rfl

theorem cell22_4123048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4123048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123048 prefixEnd_4123048 := by exact prefixLift 4123048
  have htrace : WordTrace (prefixWord ++ tailWord_4123048) baseStart_4123048 baseEnd_4123048 := by
    simpa [prefixWord, tailWord_4123048, baseEnd_4123048] using wordTrace_append hprefix tailTrace_4123048
  have hstable : (prefixWord ++ tailWord_4123048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123048).length < 2 ^ (prefixWord ++ tailWord_4123048).sum := by decide
  have hdescent : baseEnd_4123048 < baseStart_4123048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123151 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 4, 3]
def baseStart_4123151 : Nat := 118140960795 + 4123151 * 2 ^ 59
def prefixEnd_4123151 : Nat := 4983230072969 + 3 ^ 40 * 4123151 * 2
def baseEnd_4123151 : Nat := 1411438849377535257633653

theorem tailTrace_4123151 : CollatzResearch.WordTrace tailWord_4123151 prefixEnd_4123151 1411438849377535257633653 := by
  unfold tailWord_4123151
  simp only [CollatzResearch.WordTrace]
  refine ⟨150383671485535579973425307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100255780990357053315616871 150383671485535579973425307)
  ·
    refine ⟨225575507228303369960137961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150383671485535579973425307 225575507228303369960137961)
    ·
      refine ⟨169181630421227527470103471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225575507228303369960137961 169181630421227527470103471)
      ·
        refine ⟨253772445631841291205155207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169181630421227527470103471 253772445631841291205155207)
        ·
          refine ⟨380658668447761936807732811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253772445631841291205155207 380658668447761936807732811)
          ·
            refine ⟨570988002671642905211599217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380658668447761936807732811 570988002671642905211599217)
            ·
              refine ⟨428241002003732178908699413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570988002671642905211599217 428241002003732178908699413)
              ·
                refine ⟨20073796968924945886345285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428241002003732178908699413 20073796968924945886345285)
                ·
                  refine ⟨3763836931673427353689741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20073796968924945886345285 3763836931673427353689741)
                  ·
                    refine ⟨1411438849377535257633653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763836931673427353689741 1411438849377535257633653)
                    ·
                      rfl

theorem cell22_4123151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_4123151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123151 prefixEnd_4123151 := by exact prefixLift 4123151
  have htrace : WordTrace (prefixWord ++ tailWord_4123151) baseStart_4123151 baseEnd_4123151 := by
    simpa [prefixWord, tailWord_4123151, baseEnd_4123151] using wordTrace_append hprefix tailTrace_4123151
  have hstable : (prefixWord ++ tailWord_4123151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123151).length < 2 ^ (prefixWord ++ tailWord_4123151).sum := by decide
  have hdescent : baseEnd_4123151 < baseStart_4123151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123185 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_4123185 : Nat := 118140960795 + 4123185 * 2 ^ 59
def prefixEnd_4123185 : Nat := 4983230072969 + 3 ^ 40 * 4123185 * 2
def baseEnd_4123185 : Nat := 1411450488272370502283549

theorem tailTrace_4123185 : CollatzResearch.WordTrace tailWord_4123185 prefixEnd_4123185 1411450488272370502283549 := by
  unfold tailWord_4123185
  simp only [CollatzResearch.WordTrace]
  refine ⟨150384911567412403780163009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100256607711608269186775339 150384911567412403780163009)
  ·
    refine ⟨112788683675559302835122257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150384911567412403780163009 112788683675559302835122257)
    ·
      refine ⟨84591512756669477126341693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112788683675559302835122257 84591512756669477126341693)
      ·
        refine ⟨31721817283751053922378135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84591512756669477126341693 31721817283751053922378135)
        ·
          refine ⟨47582725925626580883567203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31721817283751053922378135 47582725925626580883567203)
          ·
            refine ⟨71374088888439871325350805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47582725925626580883567203 71374088888439871325350805)
            ·
              refine ⟨3345660416645618968375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71374088888439871325350805 3345660416645618968375819)
              ·
                refine ⟨5018490624968428452563729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345660416645618968375819 5018490624968428452563729)
                ·
                  refine ⟨3763867968726321339422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5018490624968428452563729 3763867968726321339422797)
                  ·
                    refine ⟨1411450488272370502283549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763867968726321339422797 1411450488272370502283549)
                    ·
                      rfl

theorem cell22_4123185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_4123185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123185 prefixEnd_4123185 := by exact prefixLift 4123185
  have htrace : WordTrace (prefixWord ++ tailWord_4123185) baseStart_4123185 baseEnd_4123185 := by
    simpa [prefixWord, tailWord_4123185, baseEnd_4123185] using wordTrace_append hprefix tailTrace_4123185
  have hstable : (prefixWord ++ tailWord_4123185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123185).length < 2 ^ (prefixWord ++ tailWord_4123185).sum := by decide
  have hdescent : baseEnd_4123185 < baseStart_4123185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123271 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 8]
def baseStart_4123271 : Nat := 118140960795 + 4123271 * 2 ^ 59
def prefixEnd_4123271 : Nat := 4983230072969 + 3 ^ 40 * 4123271 * 2
def baseEnd_4123271 : Nat := 470493309276631648211095

theorem tailTrace_4123271 : CollatzResearch.WordTrace tailWord_4123271 prefixEnd_4123271 470493309276631648211095 := by
  unfold tailWord_4123271
  simp only [CollatzResearch.WordTrace]
  refine ⟨150388048245100840467793667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100258698830067226978529111 150388048245100840467793667)
  ·
    refine ⟨225582072367651260701690501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150388048245100840467793667 225582072367651260701690501)
    ·
      refine ⟨42296638568934611381566969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225582072367651260701690501 42296638568934611381566969)
      ·
        refine ⟨31722478926700958536175227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42296638568934611381566969 31722478926700958536175227)
        ·
          refine ⟨47583718390051437804262841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31722478926700958536175227 47583718390051437804262841)
          ·
            refine ⟨35687788792538578353197131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47583718390051437804262841 35687788792538578353197131)
            ·
              refine ⟨53531683188807867529795697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35687788792538578353197131 53531683188807867529795697)
              ·
                refine ⟨40148762391605900647346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53531683188807867529795697 40148762391605900647346773)
                ·
                  refine ⟨470493309276631648211095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40148762391605900647346773 470493309276631648211095)
                  ·
                    rfl

theorem cell22_4123271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_4123271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123271 prefixEnd_4123271 := by exact prefixLift 4123271
  have htrace : WordTrace (prefixWord ++ tailWord_4123271) baseStart_4123271 baseEnd_4123271 := by
    simpa [prefixWord, tailWord_4123271, baseEnd_4123271] using wordTrace_append hprefix tailTrace_4123271
  have hstable : (prefixWord ++ tailWord_4123271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123271).length < 2 ^ (prefixWord ++ tailWord_4123271).sum := by decide
  have hdescent : baseEnd_4123271 < baseStart_4123271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123288 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_4123288 : Nat := 118140960795 + 4123288 * 2 ^ 59
def prefixEnd_4123288 : Nat := 4983230072969 + 3 ^ 40 * 4123288 * 2
def baseEnd_4123288 : Nat := 470495249092437522319411

theorem tailTrace_4123288 : CollatzResearch.WordTrace tailWord_4123288 prefixEnd_4123288 470495249092437522319411 := by
  unfold tailWord_4123288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75194334143019626185581259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100259112190692834914108345 75194334143019626185581259)
  ·
    refine ⟨112791501214529439278371889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75194334143019626185581259 112791501214529439278371889)
    ·
      refine ⟨84593625910897079458778917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112791501214529439278371889 84593625910897079458778917)
      ·
        refine ⟨15861304858293202398521047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84593625910897079458778917 15861304858293202398521047)
        ·
          refine ⟨23791957287439803597781571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15861304858293202398521047 23791957287439803597781571)
          ·
            refine ⟨35687935931159705396672357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23791957287439803597781571 35687935931159705396672357)
            ·
              refine ⟨6691487987092444761876067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35687935931159705396672357 6691487987092444761876067)
              ·
                refine ⟨10037231980638667142814101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691487987092444761876067 10037231980638667142814101)
                ·
                  refine ⟨470495249092437522319411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10037231980638667142814101 470495249092437522319411)
                  ·
                    rfl

theorem cell22_4123288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_4123288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123288 prefixEnd_4123288 := by exact prefixLift 4123288
  have htrace : WordTrace (prefixWord ++ tailWord_4123288) baseStart_4123288 baseEnd_4123288 := by
    simpa [prefixWord, tailWord_4123288, baseEnd_4123288] using wordTrace_append hprefix tailTrace_4123288
  have hstable : (prefixWord ++ tailWord_4123288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123288).length < 2 ^ (prefixWord ++ tailWord_4123288).sum := by decide
  have hdescent : baseEnd_4123288 < baseStart_4123288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123393 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4123393 : Nat := 118140960795 + 4123393 * 2 ^ 59
def prefixEnd_4123393 : Nat := 4983230072969 + 3 ^ 40 * 4123393 * 2
def baseEnd_4123393 : Nat := 1411521690923127293082911

theorem tailTrace_4123393 : CollatzResearch.WordTrace tailWord_4123393 prefixEnd_4123393 1411521690923127293082911 := by
  unfold tailWord_4123393
  simp only [CollatzResearch.WordTrace]
  refine ⟨150392497950658855303734833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100261665300439236869156555 150392497950658855303734833)
  ·
    refine ⟨112794373462994141477801125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150392497950658855303734833 112794373462994141477801125)
    ·
      refine ⟨21148945024311401527087711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112794373462994141477801125 21148945024311401527087711)
      ·
        refine ⟨31723417536467102290631567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21148945024311401527087711 31723417536467102290631567)
        ·
          refine ⟨47585126304700653435947351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31723417536467102290631567 47585126304700653435947351)
          ·
            refine ⟨71377689457050980153921027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47585126304700653435947351 71377689457050980153921027)
            ·
              refine ⟨107066534185576470230881541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71377689457050980153921027 107066534185576470230881541)
              ·
                refine ⟨20074975159795588168290289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107066534185576470230881541 20074975159795588168290289)
                ·
                  refine ⟨15056231369846691126217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20074975159795588168290289 15056231369846691126217717)
                  ·
                    refine ⟨1411521690923127293082911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15056231369846691126217717 1411521690923127293082911)
                    ·
                      rfl

theorem cell22_4123393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4123393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123393 prefixEnd_4123393 := by exact prefixLift 4123393
  have htrace : WordTrace (prefixWord ++ tailWord_4123393) baseStart_4123393 baseEnd_4123393 := by
    simpa [prefixWord, tailWord_4123393, baseEnd_4123393] using wordTrace_append hprefix tailTrace_4123393
  have hstable : (prefixWord ++ tailWord_4123393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123393).length < 2 ^ (prefixWord ++ tailWord_4123393).sum := by decide
  have hdescent : baseEnd_4123393 < baseStart_4123393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123399 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 1, 3]
def baseStart_4123399 : Nat := 118140960795 + 4123399 * 2 ^ 59
def prefixEnd_4123399 : Nat := 4983230072969 + 3 ^ 40 * 4123399 * 2
def baseEnd_4123399 : Nat := 1411523744845745277432893

theorem tailTrace_4123399 : CollatzResearch.WordTrace tailWord_4123399 prefixEnd_4123399 1411523744845745277432893 := by
  unfold tailWord_4123399
  simp only [CollatzResearch.WordTrace]
  refine ⟨150392716788637118328453251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100261811192424745552302167 150392716788637118328453251)
  ·
    refine ⟨225589075182955677492679877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150392716788637118328453251 225589075182955677492679877)
    ·
      refine ⟨42297951596804189529877477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225589075182955677492679877 42297951596804189529877477)
      ·
        refine ⟨7930865924400785536852027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42297951596804189529877477 7930865924400785536852027)
        ·
          refine ⟨11896298886601178305278041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930865924400785536852027 11896298886601178305278041)
          ·
            refine ⟨8922224164950883728958531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896298886601178305278041 8922224164950883728958531)
            ·
              refine ⟨13383336247426325593437797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922224164950883728958531 13383336247426325593437797)
              ·
                refine ⟨2509375546392436048769587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13383336247426325593437797 2509375546392436048769587)
                ·
                  refine ⟨3764063319588654073154381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509375546392436048769587 3764063319588654073154381)
                  ·
                    refine ⟨1411523744845745277432893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764063319588654073154381 1411523744845745277432893)
                    ·
                      rfl

theorem cell22_4123399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_4123399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123399 prefixEnd_4123399 := by exact prefixLift 4123399
  have htrace : WordTrace (prefixWord ++ tailWord_4123399) baseStart_4123399 baseEnd_4123399 := by
    simpa [prefixWord, tailWord_4123399, baseEnd_4123399] using wordTrace_append hprefix tailTrace_4123399
  have hstable : (prefixWord ++ tailWord_4123399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123399).length < 2 ^ (prefixWord ++ tailWord_4123399).sum := by decide
  have hdescent : baseEnd_4123399 < baseStart_4123399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123423 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 8]
def baseStart_4123423 : Nat := 118140960795 + 4123423 * 2 ^ 59
def prefixEnd_4123423 : Nat := 4983230072969 + 3 ^ 40 * 4123423 * 2
def baseEnd_4123423 : Nat := 470510653512072404944273

theorem tailTrace_4123423 : CollatzResearch.WordTrace tailWord_4123423 prefixEnd_4123423 470510653512072404944273 := by
  unfold tailWord_4123423
  simp only [CollatzResearch.WordTrace]
  refine ⟨150393592140550170427326923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100262394760366780284884615 150393592140550170427326923)
  ·
    refine ⟨225590388210825255640990385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150393592140550170427326923 225590388210825255640990385)
    ·
      refine ⟨169192791158118941730742789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225590388210825255640990385 169192791158118941730742789)
      ·
        refine ⟨31723648342147301574514273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169192791158118941730742789 31723648342147301574514273)
        ·
          refine ⟨23792736256610476180885705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31723648342147301574514273 23792736256610476180885705)
          ·
            refine ⟨17844552192457857135664279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23792736256610476180885705 17844552192457857135664279)
            ·
              refine ⟨26766828288686785703496419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17844552192457857135664279 26766828288686785703496419)
              ·
                refine ⟨40150242433030178555244629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26766828288686785703496419 40150242433030178555244629)
                ·
                  refine ⟨470510653512072404944273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40150242433030178555244629 470510653512072404944273)
                  ·
                    rfl

theorem cell22_4123423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_4123423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123423 prefixEnd_4123423 := by exact prefixLift 4123423
  have htrace : WordTrace (prefixWord ++ tailWord_4123423) baseStart_4123423 baseEnd_4123423 := by
    simpa [prefixWord, tailWord_4123423, baseEnd_4123423] using wordTrace_append hprefix tailTrace_4123423
  have hstable : (prefixWord ++ tailWord_4123423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123423).length < 2 ^ (prefixWord ++ tailWord_4123423).sum := by decide
  have hdescent : baseEnd_4123423 < baseStart_4123423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123425 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4123425 : Nat := 118140960795 + 4123425 * 2 ^ 59
def prefixEnd_4123425 : Nat := 4983230072969 + 3 ^ 40 * 4123425 * 2
def baseEnd_4123425 : Nat := 1411532645177089876282813

theorem tailTrace_4123425 : CollatzResearch.WordTrace tailWord_4123425 prefixEnd_4123425 1411532645177089876282813 := by
  unfold tailWord_4123425
  simp only [CollatzResearch.WordTrace]
  refine ⟨150393665086542924768899729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100262443391028616512599819 150393665086542924768899729)
  ·
    refine ⟨112795248814907193576674797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150393665086542924768899729 112795248814907193576674797)
    ·
      refine ⟨42298218305590197591253049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112795248814907193576674797 42298218305590197591253049)
      ·
        refine ⟨31723663729192648193439787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42298218305590197591253049 31723663729192648193439787)
        ·
          refine ⟨47585495593788972290159681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31723663729192648193439787 47585495593788972290159681)
          ·
            refine ⟨35689121695341729217619761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47585495593788972290159681 35689121695341729217619761)
            ·
              refine ⟨26766841271506296913214821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35689121695341729217619761 26766841271506296913214821)
              ·
                refine ⟨5018782738407430671227779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26766841271506296913214821 5018782738407430671227779)
                ·
                  refine ⟨7528174107611146006841669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018782738407430671227779 7528174107611146006841669)
                  ·
                    refine ⟨1411532645177089876282813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528174107611146006841669 1411532645177089876282813)
                    ·
                      rfl

theorem cell22_4123425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4123425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123425 prefixEnd_4123425 := by exact prefixLift 4123425
  have htrace : WordTrace (prefixWord ++ tailWord_4123425) baseStart_4123425 baseEnd_4123425 := by
    simpa [prefixWord, tailWord_4123425, baseEnd_4123425] using wordTrace_append hprefix tailTrace_4123425
  have hstable : (prefixWord ++ tailWord_4123425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123425).length < 2 ^ (prefixWord ++ tailWord_4123425).sum := by decide
  have hdescent : baseEnd_4123425 < baseStart_4123425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123446 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_4123446 : Nat := 118140960795 + 4123446 * 2 ^ 59
def prefixEnd_4123446 : Nat := 4983230072969 + 3 ^ 40 * 4123446 * 2
def baseEnd_4123446 : Nat := 470513277968750940502583

theorem tailTrace_4123446 : CollatzResearch.WordTrace tailWord_4123446 prefixEnd_4123446 470513277968750940502583 := by
  unfold tailWord_4123446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399651938716677834713387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100262954012977896903609461 9399651938716677834713387)
  ·
    refine ⟨14099477908075016752070081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399651938716677834713387 14099477908075016752070081)
    ·
      refine ⟨10574608431056262564052561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14099477908075016752070081 10574608431056262564052561)
      ·
        refine ⟨7930956323292196923039421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10574608431056262564052561 7930956323292196923039421)
        ·
          refine ⟨2974108621234573846139783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7930956323292196923039421 2974108621234573846139783)
          ·
            refine ⟨4461162931851860769209675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974108621234573846139783 4461162931851860769209675)
            ·
              refine ⟨6691744397777791153814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461162931851860769209675 6691744397777791153814513)
              ·
                refine ⟨5018808298333343365360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6691744397777791153814513 5018808298333343365360885)
                ·
                  refine ⟨470513277968750940502583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5018808298333343365360885 470513277968750940502583)
                  ·
                    rfl

theorem cell22_4123446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_4123446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123446 prefixEnd_4123446 := by exact prefixLift 4123446
  have htrace : WordTrace (prefixWord ++ tailWord_4123446) baseStart_4123446 baseEnd_4123446 := by
    simpa [prefixWord, tailWord_4123446, baseEnd_4123446] using wordTrace_append hprefix tailTrace_4123446
  have hstable : (prefixWord ++ tailWord_4123446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123446).length < 2 ^ (prefixWord ++ tailWord_4123446).sum := by decide
  have hdescent : baseEnd_4123446 < baseStart_4123446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123502 : List Nat := [4, 1, 2, 3, 2, 2, 8]
def baseStart_4123502 : Nat := 118140960795 + 4123502 * 2 ^ 59
def prefixEnd_4123502 : Nat := 4983230072969 + 3 ^ 40 * 4123502 * 2
def baseEnd_4123502 : Nat := 52279963105581012670651

theorem tailTrace_4123502 : CollatzResearch.WordTrace tailWord_4123502 prefixEnd_4123502 52279963105581012670651 := by
  unfold tailWord_4123502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799559188407995864931595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100264315671509311279635173 18799559188407995864931595)
  ·
    refine ⟨28199338782611993797397393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18799559188407995864931595 28199338782611993797397393)
    ·
      refine ⟨21149504086958995348048045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28199338782611993797397393 21149504086958995348048045)
      ·
        refine ⟨7931064032609623255518017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21149504086958995348048045 7931064032609623255518017)
        ·
          refine ⟨5948298024457217441638513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931064032609623255518017 5948298024457217441638513)
          ·
            refine ⟨4461223518342913081228885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5948298024457217441638513 4461223518342913081228885)
            ·
              refine ⟨52279963105581012670651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4461223518342913081228885 52279963105581012670651)
              ·
                rfl

theorem cell22_4123502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 8].length) (baseStart_4123502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123502 prefixEnd_4123502 := by exact prefixLift 4123502
  have htrace : WordTrace (prefixWord ++ tailWord_4123502) baseStart_4123502 baseEnd_4123502 := by
    simpa [prefixWord, tailWord_4123502, baseEnd_4123502] using wordTrace_append hprefix tailTrace_4123502
  have hstable : (prefixWord ++ tailWord_4123502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123502).length < 2 ^ (prefixWord ++ tailWord_4123502).sum := by decide
  have hdescent : baseEnd_4123502 < baseStart_4123502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123517 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_4123517 : Nat := 118140960795 + 4123517 * 2 ^ 59
def prefixEnd_4123517 : Nat := 4983230072969 + 3 ^ 40 * 4123517 * 2
def baseEnd_4123517 : Nat := 1411564138657232302982531

theorem tailTrace_4123517 : CollatzResearch.WordTrace tailWord_4123517 prefixEnd_4123517 1411564138657232302982531 := by
  unfold tailWord_4123517
  simp only [CollatzResearch.WordTrace]
  refine ⟨150397020602209624481248805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100264680401473082987499203 150397020602209624481248805)
  ·
    refine ⟨28199441362914304590234151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150397020602209624481248805 28199441362914304590234151)
    ·
      refine ⟨42299162044371456885351227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28199441362914304590234151 42299162044371456885351227)
      ·
        refine ⟨63448743066557185328026841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42299162044371456885351227 63448743066557185328026841)
        ·
          refine ⟨47586557299917888996020131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63448743066557185328026841 47586557299917888996020131)
          ·
            refine ⟨71379835949876833494030197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47586557299917888996020131 71379835949876833494030197)
            ·
              refine ⟨6691859620300953140065331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71379835949876833494030197 6691859620300953140065331)
              ·
                refine ⟨10037789430451429710097997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691859620300953140065331 10037789430451429710097997)
                ·
                  refine ⟨3764171036419286141286749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10037789430451429710097997 3764171036419286141286749)
                  ·
                    refine ⟨1411564138657232302982531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764171036419286141286749 1411564138657232302982531)
                    ·
                      rfl

theorem cell22_4123517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_4123517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123517 prefixEnd_4123517 := by exact prefixLift 4123517
  have htrace : WordTrace (prefixWord ++ tailWord_4123517) baseStart_4123517 baseEnd_4123517 := by
    simpa [prefixWord, tailWord_4123517, baseEnd_4123517] using wordTrace_append hprefix tailTrace_4123517
  have hstable : (prefixWord ++ tailWord_4123517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123517).length < 2 ^ (prefixWord ++ tailWord_4123517).sum := by decide
  have hdescent : baseEnd_4123517 < baseStart_4123517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123592 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_4123592 : Nat := 118140960795 + 4123592 * 2 ^ 59
def prefixEnd_4123592 : Nat := 4983230072969 + 3 ^ 40 * 4123592 * 2
def baseEnd_4123592 : Nat := 470529937563319035785767

theorem tailTrace_4123592 : CollatzResearch.WordTrace tailWord_4123592 prefixEnd_4123592 470529937563319035785767 := by
  unfold tailWord_4123592
  simp only [CollatzResearch.WordTrace]
  refine ⟨75199878038468956145114515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100266504051291941526819353 75199878038468956145114515)
  ·
    refine ⟨112799817057703434217671773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75199878038468956145114515 112799817057703434217671773)
    ·
      refine ⟨42299931396638787831626915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112799817057703434217671773 42299931396638787831626915)
      ·
        refine ⟨63449897094958181747440373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42299931396638787831626915 63449897094958181747440373)
        ·
          refine ⟨5948427852652329538822535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63449897094958181747440373 5948427852652329538822535)
          ·
            refine ⟨8922641778978494308233803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948427852652329538822535 8922641778978494308233803)
            ·
              refine ⟨13383962668467741462350705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922641778978494308233803 13383962668467741462350705)
              ·
                refine ⟨10037972001350806096763029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13383962668467741462350705 10037972001350806096763029)
                ·
                  refine ⟨470529937563319035785767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10037972001350806096763029 470529937563319035785767)
                  ·
                    rfl

theorem cell22_4123592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_4123592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123592 prefixEnd_4123592 := by exact prefixLift 4123592
  have htrace : WordTrace (prefixWord ++ tailWord_4123592) baseStart_4123592 baseEnd_4123592 := by
    simpa [prefixWord, tailWord_4123592, baseEnd_4123592] using wordTrace_append hprefix tailTrace_4123592
  have hstable : (prefixWord ++ tailWord_4123592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123592).length < 2 ^ (prefixWord ++ tailWord_4123592).sum := by decide
  have hdescent : baseEnd_4123592 < baseStart_4123592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123609 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 4]
def baseStart_4123609 : Nat := 118140960795 + 4123609 * 2 ^ 59
def prefixEnd_4123609 : Nat := 4983230072969 + 3 ^ 40 * 4123609 * 2
def baseEnd_4123609 : Nat := 470531877379124909894083

theorem tailTrace_4123609 : CollatzResearch.WordTrace tailWord_4123609 prefixEnd_4123609 470531877379124909894083 := by
  unfold tailWord_4123609
  simp only [CollatzResearch.WordTrace]
  refine ⟨150400376117876324193597881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100266917411917549462398587 150400376117876324193597881)
  ·
    refine ⟨112800282088407243145198411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150400376117876324193597881 112800282088407243145198411)
    ·
      refine ⟨169200423132610864717797617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112800282088407243145198411 169200423132610864717797617)
      ·
        refine ⟨126900317349458148538348213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169200423132610864717797617 126900317349458148538348213)
        ·
          refine ⟨11896904751511701425470145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126900317349458148538348213 11896904751511701425470145)
          ·
            refine ⟨8922678563633776069102609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896904751511701425470145 8922678563633776069102609)
            ·
              refine ⟨6692008922725332051826957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8922678563633776069102609 6692008922725332051826957)
              ·
                refine ⟨2509503346021999519435109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6692008922725332051826957 2509503346021999519435109)
                ·
                  refine ⟨470531877379124909894083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509503346021999519435109 470531877379124909894083)
                  ·
                    rfl

theorem cell22_4123609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_4123609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123609 prefixEnd_4123609 := by exact prefixLift 4123609
  have htrace : WordTrace (prefixWord ++ tailWord_4123609) baseStart_4123609 baseEnd_4123609 := by
    simpa [prefixWord, tailWord_4123609, baseEnd_4123609] using wordTrace_append hprefix tailTrace_4123609
  have hstable : (prefixWord ++ tailWord_4123609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123609).length < 2 ^ (prefixWord ++ tailWord_4123609).sum := by decide
  have hdescent : baseEnd_4123609 < baseStart_4123609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123624 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4123624 : Nat := 118140960795 + 4123624 * 2 ^ 59
def prefixEnd_4123624 : Nat := 4983230072969 + 3 ^ 40 * 4123624 * 2
def baseEnd_4123624 : Nat := 1411600766943919690557203

theorem tailTrace_4123624 : CollatzResearch.WordTrace tailWord_4123624 prefixEnd_4123624 1411600766943919690557203 := by
  unfold tailWord_4123624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75200461606410990877696963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100267282141881321170262617 75200461606410990877696963)
  ·
    refine ⟨112800692409616486316545445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75200461606410990877696963 112800692409616486316545445)
    ·
      refine ⟨21150129826803091184352271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112800692409616486316545445 21150129826803091184352271)
      ·
        refine ⟨31725194740204636776528407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150129826803091184352271 31725194740204636776528407)
        ·
          refine ⟨47587792110306955164792611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31725194740204636776528407 47587792110306955164792611)
          ·
            refine ⟨71381688165460432747188917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47587792110306955164792611 71381688165460432747188917)
            ·
              refine ⟨6692033265511915570048961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71381688165460432747188917 6692033265511915570048961)
              ·
                refine ⟨5019024949133936677536721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6692033265511915570048961 5019024949133936677536721)
                ·
                  refine ⟨3764268711850452508152541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019024949133936677536721 3764268711850452508152541)
                  ·
                    refine ⟨1411600766943919690557203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764268711850452508152541 1411600766943919690557203)
                    ·
                      rfl

theorem cell22_4123624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4123624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123624 prefixEnd_4123624 := by exact prefixLift 4123624
  have htrace : WordTrace (prefixWord ++ tailWord_4123624) baseStart_4123624 baseEnd_4123624 := by
    simpa [prefixWord, tailWord_4123624, baseEnd_4123624] using wordTrace_append hprefix tailTrace_4123624
  have hstable : (prefixWord ++ tailWord_4123624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123624).length < 2 ^ (prefixWord ++ tailWord_4123624).sum := by decide
  have hdescent : baseEnd_4123624 < baseStart_4123624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123682 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_4123682 : Nat := 118140960795 + 4123682 * 2 ^ 59
def prefixEnd_4123682 : Nat := 4983230072969 + 3 ^ 40 * 4123682 * 2
def baseEnd_4123682 : Nat := 470540207176408957535675

theorem tailTrace_4123682 : CollatzResearch.WordTrace tailWord_4123682 prefixEnd_4123682 470540207176408957535675 := by
  unfold tailWord_4123682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600759661652964415251325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100268692431074571774003533 37600759661652964415251325)
  ·
    refine ⟨14100284873119861655719247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37600759661652964415251325 14100284873119861655719247)
    ·
      refine ⟨21150427309679792483578871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14100284873119861655719247 21150427309679792483578871)
      ·
        refine ⟨31725640964519688725368307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150427309679792483578871 31725640964519688725368307)
        ·
          refine ⟨47588461446779533088052461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31725640964519688725368307 47588461446779533088052461)
          ·
            refine ⟨17845673042542324908019673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47588461446779533088052461 17845673042542324908019673)
            ·
              refine ⟨13384254781906743681014755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845673042542324908019673 13384254781906743681014755)
              ·
                refine ⟨20076382172860115521522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384254781906743681014755 20076382172860115521522133)
                ·
                  refine ⟨470540207176408957535675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20076382172860115521522133 470540207176408957535675)
                  ·
                    rfl

theorem cell22_4123682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_4123682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123682 prefixEnd_4123682 := by exact prefixLift 4123682
  have htrace : WordTrace (prefixWord ++ tailWord_4123682) baseStart_4123682 baseEnd_4123682 := by
    simpa [prefixWord, tailWord_4123682, baseEnd_4123682] using wordTrace_append hprefix tailTrace_4123682
  have hstable : (prefixWord ++ tailWord_4123682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123682).length < 2 ^ (prefixWord ++ tailWord_4123682).sum := by decide
  have hdescent : baseEnd_4123682 < baseStart_4123682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123712 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_4123712 : Nat := 118140960795 + 4123712 * 2 ^ 59
def prefixEnd_4123712 : Nat := 4983230072969 + 3 ^ 40 * 4123712 * 2
def baseEnd_4123712 : Nat := 1411630891142316794356933

theorem tailTrace_4123712 : CollatzResearch.WordTrace tailWord_4123712 prefixEnd_4123712 1411630891142316794356933 := by
  unfold tailWord_4123712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75202066418251586392298695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100269421891002115189731593 75202066418251586392298695)
  ·
    refine ⟨112803099627377379588448043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75202066418251586392298695 112803099627377379588448043)
    ·
      refine ⟨169204649441066069382672065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112803099627377379588448043 169204649441066069382672065)
      ·
        refine ⟨126903487080799552037004049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169204649441066069382672065 126903487080799552037004049)
        ·
          refine ⟨95177615310599664027753037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126903487080799552037004049 95177615310599664027753037)
          ·
            refine ⟨35691605741474874010407389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95177615310599664027753037 35691605741474874010407389)
            ·
              refine ⟨13384352153053077753902771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35691605741474874010407389 13384352153053077753902771)
              ·
                refine ⟨20076528229579616630854157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384352153053077753902771 20076528229579616630854157)
                ·
                  refine ⟨7528698086092356236570309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20076528229579616630854157 7528698086092356236570309)
                  ·
                    refine ⟨1411630891142316794356933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528698086092356236570309 1411630891142316794356933)
                    ·
                      rfl

theorem cell22_4123712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_4123712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123712 prefixEnd_4123712 := by exact prefixLift 4123712
  have htrace : WordTrace (prefixWord ++ tailWord_4123712) baseStart_4123712 baseEnd_4123712 := by
    simpa [prefixWord, tailWord_4123712, baseEnd_4123712] using wordTrace_append hprefix tailTrace_4123712
  have hstable : (prefixWord ++ tailWord_4123712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123712).length < 2 ^ (prefixWord ++ tailWord_4123712).sum := by decide
  have hdescent : baseEnd_4123712 < baseStart_4123712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123744 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_4123744 : Nat := 118140960795 + 4123744 * 2 ^ 59
def prefixEnd_4123744 : Nat := 4983230072969 + 3 ^ 40 * 4123744 * 2
def baseEnd_4123744 : Nat := 470547281798759792518945

theorem tailTrace_4123744 : CollatzResearch.WordTrace tailWord_4123744 prefixEnd_4123744 470547281798759792518945 := by
  unfold tailWord_4123744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75202649986193621124881143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100270199981591494833174857 75202649986193621124881143)
  ·
    refine ⟨112803974979290431687321715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75202649986193621124881143 112803974979290431687321715)
    ·
      refine ⟨169205962468935647530982573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112803974979290431687321715 169205962468935647530982573)
      ·
        refine ⟨63452235925850867824118465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169205962468935647530982573 63452235925850867824118465)
        ·
          refine ⟨47589176944388150868088849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63452235925850867824118465 47589176944388150868088849)
          ·
            refine ⟨35691882708291113151066637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47589176944388150868088849 35691882708291113151066637)
            ·
              refine ⟨13384456015609167431649989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35691882708291113151066637 13384456015609167431649989)
              ·
                refine ⟨2509585502926718893434373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13384456015609167431649989 2509585502926718893434373)
                ·
                  refine ⟨470547281798759792518945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509585502926718893434373 470547281798759792518945)
                  ·
                    rfl

theorem cell22_4123744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_4123744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123744 prefixEnd_4123744 := by exact prefixLift 4123744
  have htrace : WordTrace (prefixWord ++ tailWord_4123744) baseStart_4123744 baseEnd_4123744 := by
    simpa [prefixWord, tailWord_4123744, baseEnd_4123744] using wordTrace_append hprefix tailTrace_4123744
  have hstable : (prefixWord ++ tailWord_4123744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123744).length < 2 ^ (prefixWord ++ tailWord_4123744).sum := by decide
  have hdescent : baseEnd_4123744 < baseStart_4123744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123759 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 2, 3]
def baseStart_4123759 : Nat := 118140960795 + 4123759 * 2 ^ 59
def prefixEnd_4123759 : Nat := 4983230072969 + 3 ^ 40 * 4123759 * 2
def baseEnd_4123759 : Nat := 1411646980202824338431789

theorem tailTrace_4123759 : CollatzResearch.WordTrace tailWord_4123759 prefixEnd_4123759 1411646980202824338431789 := by
  unfold tailWord_4123759
  simp only [CollatzResearch.WordTrace]
  refine ⟨150405847067332899811558331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100270564711555266541038887 150405847067332899811558331)
  ·
    refine ⟨225608770600999349717337497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150405847067332899811558331 225608770600999349717337497)
    ·
      refine ⟨169206577950749512288003123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225608770600999349717337497 169206577950749512288003123)
      ·
        refine ⟨253809866926124268432004685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169206577950749512288003123 253809866926124268432004685)
        ·
          refine ⟨95178700097296600662001757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253809866926124268432004685 95178700097296600662001757)
          ·
            refine ⟨35692012536486225248250659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95178700097296600662001757 35692012536486225248250659)
            ·
              refine ⟨53538018804729337872375989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35692012536486225248250659 53538018804729337872375989)
              ·
                refine ⟨5019189262943375425535249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53538018804729337872375989 5019189262943375425535249)
                ·
                  refine ⟨3764391947207531569151437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019189262943375425535249 3764391947207531569151437)
                  ·
                    refine ⟨1411646980202824338431789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764391947207531569151437 1411646980202824338431789)
                    ·
                      rfl

theorem cell22_4123759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_4123759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123759 prefixEnd_4123759 := by exact prefixLift 4123759
  have htrace : WordTrace (prefixWord ++ tailWord_4123759) baseStart_4123759 baseEnd_4123759 := by
    simpa [prefixWord, tailWord_4123759, baseEnd_4123759] using wordTrace_append hprefix tailTrace_4123759
  have hstable : (prefixWord ++ tailWord_4123759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123759).length < 2 ^ (prefixWord ++ tailWord_4123759).sum := by decide
  have hdescent : baseEnd_4123759 < baseStart_4123759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123810 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4123810 : Nat := 118140960795 + 4123810 * 2 ^ 59
def prefixEnd_4123810 : Nat := 4983230072969 + 3 ^ 40 * 4123810 * 2
def baseEnd_4123810 : Nat := 1411664438545077205406633

theorem tailTrace_4123810 : CollatzResearch.WordTrace tailWord_4123810 prefixEnd_4123810 1411664438545077205406633 := by
  unfold tailWord_4123810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601926797537033880416221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100271804793432090347776589 37601926797537033880416221)
  ·
    refine ⟨14100722549076387705156083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37601926797537033880416221 14100722549076387705156083)
    ·
      refine ⟨21151083823614581557734125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14100722549076387705156083 21151083823614581557734125)
      ·
        refine ⟨7931656433855468084150297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21151083823614581557734125 7931656433855468084150297)
        ·
          refine ⟨5948742325391601063112723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931656433855468084150297 5948742325391601063112723)
          ·
            refine ⟨8923113488087401594669085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948742325391601063112723 8923113488087401594669085)
            ·
              refine ⟨3346167558032775598000907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923113488087401594669085 3346167558032775598000907)
              ·
                refine ⟨5019251337049163397001361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346167558032775598000907 5019251337049163397001361)
                ·
                  refine ⟨3764438502786872547751021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019251337049163397001361 3764438502786872547751021)
                  ·
                    refine ⟨1411664438545077205406633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764438502786872547751021 1411664438545077205406633)
                    ·
                      rfl

theorem cell22_4123810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4123810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123810 prefixEnd_4123810 := by exact prefixLift 4123810
  have htrace : WordTrace (prefixWord ++ tailWord_4123810) baseStart_4123810 baseEnd_4123810 := by
    simpa [prefixWord, tailWord_4123810, baseEnd_4123810] using wordTrace_append hprefix tailTrace_4123810
  have hstable : (prefixWord ++ tailWord_4123810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123810).length < 2 ^ (prefixWord ++ tailWord_4123810).sum := by decide
  have hdescent : baseEnd_4123810 < baseStart_4123810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123832 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_4123832 : Nat := 118140960795 + 4123832 * 2 ^ 59
def prefixEnd_4123832 : Nat := 4983230072969 + 3 ^ 40 * 4123832 * 2
def baseEnd_4123832 : Nat := 1411671969594676481356565

theorem tailTrace_4123832 : CollatzResearch.WordTrace tailWord_4123832 prefixEnd_4123832 1411671969594676481356565 := by
  unfold tailWord_4123832
  simp only [CollatzResearch.WordTrace]
  refine ⟨75204254798034216639482875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100272339730712288852643833 75204254798034216639482875)
  ·
    refine ⟨112806382197051324959224313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75204254798034216639482875 112806382197051324959224313)
    ·
      refine ⟨84604786647788493719418235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112806382197051324959224313 84604786647788493719418235)
      ·
        refine ⟨126907179971682740579127353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84604786647788493719418235 126907179971682740579127353)
        ·
          refine ⟨95180384978762055434345515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126907179971682740579127353 95180384978762055434345515)
          ·
            refine ⟨142770577468143083151518273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95180384978762055434345515 142770577468143083151518273)
            ·
              refine ⟨107077933101107312363638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142770577468143083151518273 107077933101107312363638705)
              ·
                refine ⟨80308449825830484272729029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107077933101107312363638705 80308449825830484272729029)
                ·
                  refine ⟨15057834342343215801136693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80308449825830484272729029 15057834342343215801136693)
                  ·
                    refine ⟨1411671969594676481356565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15057834342343215801136693 1411671969594676481356565)
                    ·
                      rfl

theorem cell22_4123832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_4123832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123832 prefixEnd_4123832 := by exact prefixLift 4123832
  have htrace : WordTrace (prefixWord ++ tailWord_4123832) baseStart_4123832 baseEnd_4123832 := by
    simpa [prefixWord, tailWord_4123832, baseEnd_4123832] using wordTrace_append hprefix tailTrace_4123832
  have hstable : (prefixWord ++ tailWord_4123832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123832).length < 2 ^ (prefixWord ++ tailWord_4123832).sum := by decide
  have hdescent : baseEnd_4123832 < baseStart_4123832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123907 : List Nat := [1, 1, 1, 3, 2, 14]
def baseStart_4123907 : Nat := 118140960795 + 4123907 * 2 ^ 59
def prefixEnd_4123907 : Nat := 4983230072969 + 3 ^ 40 * 4123907 * 2
def baseEnd_4123907 : Nat := 17428365970708657848535

theorem tailTrace_4123907 : CollatzResearch.WordTrace tailWord_4123907 prefixEnd_4123907 17428365970708657848535 := by
  unfold tailWord_4123907
  simp only [CollatzResearch.WordTrace]
  refine ⟨150411245070796721087945975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100274163380531147391963983 150411245070796721087945975)
  ·
    refine ⟨225616867606195081631918963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150411245070796721087945975 225616867606195081631918963)
    ·
      refine ⟨338425301409292622447878445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225616867606195081631918963 338425301409292622447878445)
      ·
        refine ⟨126909488028484733417954417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338425301409292622447878445 126909488028484733417954417)
        ·
          refine ⟨95182116021363550063465813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126909488028484733417954417 95182116021363550063465813)
          ·
            refine ⟨17428365970708657848535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 95182116021363550063465813 17428365970708657848535)
            ·
              rfl

theorem cell22_4123907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 14].length) (baseStart_4123907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123907 prefixEnd_4123907 := by exact prefixLift 4123907
  have htrace : WordTrace (prefixWord ++ tailWord_4123907) baseStart_4123907 baseEnd_4123907 := by
    simpa [prefixWord, tailWord_4123907, baseEnd_4123907] using wordTrace_append hprefix tailTrace_4123907
  have hstable : (prefixWord ++ tailWord_4123907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123907).length < 2 ^ (prefixWord ++ tailWord_4123907).sum := by decide
  have hdescent : baseEnd_4123907 < baseStart_4123907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123909 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4123909 : Nat := 118140960795 + 4123909 * 2 ^ 59
def prefixEnd_4123909 : Nat := 4983230072969 + 3 ^ 40 * 4123909 * 2
def baseEnd_4123909 : Nat := 1411698328268273947181329

theorem tailTrace_4123909 : CollatzResearch.WordTrace tailWord_4123909 prefixEnd_4123909 1411698328268273947181329 := by
  unfold tailWord_4123909
  simp only [CollatzResearch.WordTrace]
  refine ⟨150411318016789475429518781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100274212011192983619679187 150411318016789475429518781)
  ·
    refine ⟨56404244256296053286069543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150411318016789475429518781 56404244256296053286069543)
    ·
      refine ⟨84606366384444079929104315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56404244256296053286069543 84606366384444079929104315)
      ·
        refine ⟨126909549576666119893656473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84606366384444079929104315 126909549576666119893656473)
        ·
          refine ⟨95182162182499589920242355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126909549576666119893656473 95182162182499589920242355)
          ·
            refine ⟨142773243273749384880363533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95182162182499589920242355 142773243273749384880363533)
            ·
              refine ⟨53539966227656019330136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142773243273749384880363533 53539966227656019330136325)
              ·
                refine ⟨10038743667685503624400561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53539966227656019330136325 10038743667685503624400561)
                ·
                  refine ⟨7529057750764127718300421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038743667685503624400561 7529057750764127718300421)
                  ·
                    refine ⟨1411698328268273947181329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529057750764127718300421 1411698328268273947181329)
                    ·
                      rfl

theorem cell22_4123909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4123909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123909 prefixEnd_4123909 := by exact prefixLift 4123909
  have htrace : WordTrace (prefixWord ++ tailWord_4123909) baseStart_4123909 baseEnd_4123909 := by
    simpa [prefixWord, tailWord_4123909, baseEnd_4123909] using wordTrace_append hprefix tailTrace_4123909
  have hstable : (prefixWord ++ tailWord_4123909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123909).length < 2 ^ (prefixWord ++ tailWord_4123909).sum := by decide
  have hdescent : baseEnd_4123909 < baseStart_4123909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123941 : List Nat := [1, 3, 1, 2, 4, 2, 3, 6]
def baseStart_4123941 : Nat := 118140960795 + 4123941 * 2 ^ 59
def prefixEnd_4123941 : Nat := 4983230072969 + 3 ^ 40 * 4123941 * 2
def baseEnd_4123941 : Nat := 156856586946915170042359

theorem tailTrace_4123941 : CollatzResearch.WordTrace tailWord_4123941 prefixEnd_4123941 156856586946915170042359 := by
  unfold tailWord_4123941
  simp only [CollatzResearch.WordTrace]
  refine ⟨150412485152673544894683677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100274990101782363263122451 150412485152673544894683677)
  ·
    refine ⟨56404681932252579335506379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150412485152673544894683677 56404681932252579335506379)
    ·
      refine ⟨84607022898378869003259569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56404681932252579335506379 84607022898378869003259569)
      ·
        refine ⟨63455267173784151752444677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84607022898378869003259569 63455267173784151752444677)
        ·
          refine ⟨11897862595084528453583377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63455267173784151752444677 11897862595084528453583377)
          ·
            refine ⟨8923396946313396340187533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11897862595084528453583377 8923396946313396340187533)
            ·
              refine ⟨3346273854867523627570325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923396946313396340187533 3346273854867523627570325)
              ·
                refine ⟨156856586946915170042359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3346273854867523627570325 156856586946915170042359)
                ·
                  rfl

theorem cell22_4123941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 6].length) (baseStart_4123941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123941 prefixEnd_4123941 := by exact prefixLift 4123941
  have htrace : WordTrace (prefixWord ++ tailWord_4123941) baseStart_4123941 baseEnd_4123941 := by
    simpa [prefixWord, tailWord_4123941, baseEnd_4123941] using wordTrace_append hprefix tailTrace_4123941
  have hstable : (prefixWord ++ tailWord_4123941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123941).length < 2 ^ (prefixWord ++ tailWord_4123941).sum := by decide
  have hdescent : baseEnd_4123941 < baseStart_4123941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123958 : List Nat := [5, 1, 2, 3, 1, 1, 9]
def baseStart_4123958 : Nat := 118140960795 + 4123958 * 2 ^ 59
def prefixEnd_4123958 : Nat := 4983230072969 + 3 ^ 40 * 4123958 * 2
def baseEnd_4123958 : Nat := 52285744517394598248377

theorem tailTrace_4123958 : CollatzResearch.WordTrace tailWord_4123958 prefixEnd_4123958 52285744517394598248377 := by
  unfold tailWord_4123958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400819074600747299878283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100275403462407971198701685 9400819074600747299878283)
  ·
    refine ⟨14101228611901120949817425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400819074600747299878283 14101228611901120949817425)
    ·
      refine ⟨10575921458925840712363069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14101228611901120949817425 10575921458925840712363069)
      ·
        refine ⟨3965970547097190267136151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10575921458925840712363069 3965970547097190267136151)
        ·
          refine ⟨5948955820645785400704227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965970547097190267136151 5948955820645785400704227)
          ·
            refine ⟨8923433730968678101056341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948955820645785400704227 8923433730968678101056341)
            ·
              refine ⟨52285744517394598248377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8923433730968678101056341 52285744517394598248377)
              ·
                rfl

theorem cell22_4123958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 9].length) (baseStart_4123958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123958 prefixEnd_4123958 := by exact prefixLift 4123958
  have htrace : WordTrace (prefixWord ++ tailWord_4123958) baseStart_4123958 baseEnd_4123958 := by
    simpa [prefixWord, tailWord_4123958, baseEnd_4123958] using wordTrace_append hprefix tailTrace_4123958
  have hstable : (prefixWord ++ tailWord_4123958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123958).length < 2 ^ (prefixWord ++ tailWord_4123958).sum := by decide
  have hdescent : baseEnd_4123958 < baseStart_4123958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4123984 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_4123984 : Nat := 118140960795 + 4123984 * 2 ^ 59
def prefixEnd_4123984 : Nat := 4983230072969 + 3 ^ 40 * 4123984 * 2
def baseEnd_4123984 : Nat := 1411724002300998751556099

theorem tailTrace_4123984 : CollatzResearch.WordTrace tailWord_4123984 prefixEnd_4123984 1411724002300998751556099 := by
  unfold tailWord_4123984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207026745758881619249503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100276035661011842158999337 75207026745758881619249503)
  ·
    refine ⟨112810540118638322428874255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207026745758881619249503 112810540118638322428874255)
    ·
      refine ⟨169215810177957483643311383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112810540118638322428874255 169215810177957483643311383)
      ·
        refine ⟨253823715266936225464967075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169215810177957483643311383 253823715266936225464967075)
        ·
          refine ⟨380735572900404338197450613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253823715266936225464967075 380735572900404338197450613)
          ·
            refine ⟨35693959959412906706010995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380735572900404338197450613 35693959959412906706010995)
            ·
              refine ⟨53540939939119360059016493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35693959959412906706010995 53540939939119360059016493)
              ·
                refine ⟨20077852477169760022131185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53540939939119360059016493 20077852477169760022131185)
                ·
                  refine ⟨15058389357877320016598389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20077852477169760022131185 15058389357877320016598389)
                  ·
                    refine ⟨1411724002300998751556099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15058389357877320016598389 1411724002300998751556099)
                    ·
                      rfl

theorem cell22_4123984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_4123984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4123984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4123984 prefixEnd_4123984 := by exact prefixLift 4123984
  have htrace : WordTrace (prefixWord ++ tailWord_4123984) baseStart_4123984 baseEnd_4123984 := by
    simpa [prefixWord, tailWord_4123984, baseEnd_4123984] using wordTrace_append hprefix tailTrace_4123984
  have hstable : (prefixWord ++ tailWord_4123984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4123984).length < 2 ^ (prefixWord ++ tailWord_4123984).sum := by decide
  have hdescent : baseEnd_4123984 < baseStart_4123984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4123984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124007 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4124007 : Nat := 118140960795 + 4124007 * 2 ^ 59
def prefixEnd_4124007 : Nat := 4983230072969 + 3 ^ 40 * 4124007 * 2
def baseEnd_4124007 : Nat := 1411731875671034358231029

theorem tailTrace_4124007 : CollatzResearch.WordTrace tailWord_4124007 prefixEnd_4124007 1411731875671034358231029 := by
  unfold tailWord_4124007
  simp only [CollatzResearch.WordTrace]
  refine ⟨150414892370434438166586275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100276594913622958777724183 150414892370434438166586275)
  ·
    refine ⟨225622338555651657249879413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150414892370434438166586275 225622338555651657249879413)
    ·
      refine ⟨21152094239592342867176195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225622338555651657249879413 21152094239592342867176195)
      ·
        refine ⟨31728141359388514300764293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152094239592342867176195 31728141359388514300764293)
        ·
          refine ⟨5949026504885346431393305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31728141359388514300764293 5949026504885346431393305)
          ·
            refine ⟨4461769878664009823544979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5949026504885346431393305 4461769878664009823544979)
            ·
              refine ⟨6692654817996014735317469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461769878664009823544979 6692654817996014735317469)
              ·
                refine ⟨2509745556748505525744051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6692654817996014735317469 2509745556748505525744051)
                ·
                  refine ⟨3764618335122758288616077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509745556748505525744051 3764618335122758288616077)
                  ·
                    refine ⟨1411731875671034358231029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764618335122758288616077 1411731875671034358231029)
                    ·
                      rfl

theorem cell22_4124007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4124007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124007 prefixEnd_4124007 := by exact prefixLift 4124007
  have htrace : WordTrace (prefixWord ++ tailWord_4124007) baseStart_4124007 baseEnd_4124007 := by
    simpa [prefixWord, tailWord_4124007, baseEnd_4124007] using wordTrace_append hprefix tailTrace_4124007
  have hstable : (prefixWord ++ tailWord_4124007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124007).length < 2 ^ (prefixWord ++ tailWord_4124007).sum := by decide
  have hdescent : baseEnd_4124007 < baseStart_4124007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124016 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_4124016 : Nat := 118140960795 + 4124016 * 2 ^ 59
def prefixEnd_4124016 : Nat := 4983230072969 + 3 ^ 40 * 4124016 * 2
def baseEnd_4124016 : Nat := 1411734956554961334756001

theorem tailTrace_4124016 : CollatzResearch.WordTrace tailWord_4124016 prefixEnd_4124016 1411734956554961334756001 := by
  unfold tailWord_4124016
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207610313700916351831951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100276813751601221802442601 75207610313700916351831951)
  ·
    refine ⟨112811415470551374527747927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207610313700916351831951 112811415470551374527747927)
    ·
      refine ⟨169217123205827061791621891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112811415470551374527747927 169217123205827061791621891)
      ·
        refine ⟨253825684808740592687432837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169217123205827061791621891 253825684808740592687432837)
        ·
          refine ⟨47592315901638861128893657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253825684808740592687432837 47592315901638861128893657)
          ·
            refine ⟨35694236926229145846670243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47592315901638861128893657 35694236926229145846670243)
            ·
              refine ⟨53541355389343718770005365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35694236926229145846670243 53541355389343718770005365)
              ·
                refine ⟨5019502067750973634688003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53541355389343718770005365 5019502067750973634688003)
                ·
                  refine ⟨7529253101626460452032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019502067750973634688003 7529253101626460452032005)
                  ·
                    refine ⟨1411734956554961334756001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529253101626460452032005 1411734956554961334756001)
                    ·
                      rfl

theorem cell22_4124016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_4124016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124016 prefixEnd_4124016 := by exact prefixLift 4124016
  have htrace : WordTrace (prefixWord ++ tailWord_4124016) baseStart_4124016 baseEnd_4124016 := by
    simpa [prefixWord, tailWord_4124016, baseEnd_4124016] using wordTrace_append hprefix tailTrace_4124016
  have hstable : (prefixWord ++ tailWord_4124016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124016).length < 2 ^ (prefixWord ++ tailWord_4124016).sum := by decide
  have hdescent : baseEnd_4124016 < baseStart_4124016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124050 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4124050 : Nat := 118140960795 + 4124050 * 2 ^ 59
def prefixEnd_4124050 : Nat := 4983230072969 + 3 ^ 40 * 4124050 * 2
def baseEnd_4124050 : Nat := 1411746595449796579405897

theorem tailTrace_4124050 : CollatzResearch.WordTrace tailWord_4124050 prefixEnd_4124050 1411746595449796579405897 := by
  unfold tailWord_4124050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604115177319664127600401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100277640472852437673601069 37604115177319664127600401)
  ·
    refine ⟨28203086382989748095700301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37604115177319664127600401 28203086382989748095700301)
    ·
      refine ⟨10576157393621155535887613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28203086382989748095700301 10576157393621155535887613)
      ·
        refine ⟨3966059022607933325957855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10576157393621155535887613 3966059022607933325957855)
        ·
          refine ⟨5949088533911899988936783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966059022607933325957855 5949088533911899988936783)
          ·
            refine ⟨8923632800867849983405175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949088533911899988936783 8923632800867849983405175)
            ·
              refine ⟨13385449201301774975107763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923632800867849983405175 13385449201301774975107763)
              ·
                refine ⟨20078173801952662462661645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385449201301774975107763 20078173801952662462661645)
                ·
                  refine ⟨7529315175732248423498117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20078173801952662462661645 7529315175732248423498117)
                  ·
                    refine ⟨1411746595449796579405897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529315175732248423498117 1411746595449796579405897)
                    ·
                      rfl

theorem cell22_4124050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4124050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124050 prefixEnd_4124050 := by exact prefixLift 4124050
  have htrace : WordTrace (prefixWord ++ tailWord_4124050) baseStart_4124050 baseEnd_4124050 := by
    simpa [prefixWord, tailWord_4124050, baseEnd_4124050] using wordTrace_append hprefix tailTrace_4124050
  have hstable : (prefixWord ++ tailWord_4124050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124050).length < 2 ^ (prefixWord ++ tailWord_4124050).sum := by decide
  have hdescent : baseEnd_4124050 < baseStart_4124050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124108 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_4124108 : Nat := 118140960795 + 4124108 * 2 ^ 59
def prefixEnd_4124108 : Nat := 4983230072969 + 3 ^ 40 * 4124108 * 2
def baseEnd_4124108 : Nat := 1411766450035103761455719

theorem tailTrace_4124108 : CollatzResearch.WordTrace tailWord_4124108 prefixEnd_4124108 1411766450035103761455719 := by
  unfold tailWord_4124108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75209288071534266208006489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100279050762045688277341985 75209288071534266208006489)
  ·
    refine ⟨56406966053650699656004867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75209288071534266208006489 56406966053650699656004867)
    ·
      refine ⟨84610449080476049484007301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56406966053650699656004867 84610449080476049484007301)
      ·
        refine ⟨15864459202589259278251369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84610449080476049484007301 15864459202589259278251369)
        ·
          refine ⟨11898344401941944458688527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15864459202589259278251369 11898344401941944458688527)
          ·
            refine ⟨17847516602912916688032791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898344401941944458688527 17847516602912916688032791)
            ·
              refine ⟨26771274904369375032049187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847516602912916688032791 26771274904369375032049187)
              ·
                refine ⟨40156912356554062548073781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26771274904369375032049187 40156912356554062548073781)
                ·
                  refine ⟨3764710533426943363881917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40156912356554062548073781 3764710533426943363881917)
                  ·
                    refine ⟨1411766450035103761455719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764710533426943363881917 1411766450035103761455719)
                    ·
                      rfl

theorem cell22_4124108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_4124108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124108 prefixEnd_4124108 := by exact prefixLift 4124108
  have htrace : WordTrace (prefixWord ++ tailWord_4124108) baseStart_4124108 baseEnd_4124108 := by
    simpa [prefixWord, tailWord_4124108, baseEnd_4124108] using wordTrace_append hprefix tailTrace_4124108
  have hstable : (prefixWord ++ tailWord_4124108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124108).length < 2 ^ (prefixWord ++ tailWord_4124108).sum := by decide
  have hdescent : baseEnd_4124108 < baseStart_4124108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124136 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4124136 : Nat := 118140960795 + 4124136 * 2 ^ 59
def prefixEnd_4124136 : Nat := 4983230072969 + 3 ^ 40 * 4124136 * 2
def baseEnd_4124136 : Nat := 1411776035007321021755633

theorem tailTrace_4124136 : CollatzResearch.WordTrace tailWord_4124136 prefixEnd_4124136 1411776035007321021755633 := by
  unfold tailWord_4124136
  simp only [CollatzResearch.WordTrace]
  refine ⟨75209798693483546599016131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100279731591311395465354841 75209798693483546599016131)
  ·
    refine ⟨112814698040225319898524197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75209798693483546599016131 112814698040225319898524197)
    ·
      refine ⟨21152755882542247480973287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112814698040225319898524197 21152755882542247480973287)
      ·
        refine ⟨31729133823813371221459931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152755882542247480973287 31729133823813371221459931)
        ·
          refine ⟨47593700735720056832189897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31729133823813371221459931 47593700735720056832189897)
          ·
            refine ⟨35695275551790042624142423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47593700735720056832189897 35695275551790042624142423)
            ·
              refine ⟨53542913327685063936213635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35695275551790042624142423 53542913327685063936213635)
              ·
                refine ⟨80314369991527595904320453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53542913327685063936213635 80314369991527595904320453)
                ·
                  refine ⟨15058944373411424232060085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80314369991527595904320453 15058944373411424232060085)
                  ·
                    refine ⟨1411776035007321021755633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15058944373411424232060085 1411776035007321021755633)
                    ·
                      rfl

theorem cell22_4124136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4124136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124136 prefixEnd_4124136 := by exact prefixLift 4124136
  have htrace : WordTrace (prefixWord ++ tailWord_4124136) baseStart_4124136 baseEnd_4124136 := by
    simpa [prefixWord, tailWord_4124136, baseEnd_4124136] using wordTrace_append hprefix tailTrace_4124136
  have hstable : (prefixWord ++ tailWord_4124136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124136).length < 2 ^ (prefixWord ++ tailWord_4124136).sum := by decide
  have hdescent : baseEnd_4124136 < baseStart_4124136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124138 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_4124138 : Nat := 118140960795 + 4124138 * 2 ^ 59
def prefixEnd_4124138 : Nat := 4983230072969 + 3 ^ 40 * 4124138 * 2
def baseEnd_4124138 : Nat := 470592239882731227735209

theorem tailTrace_4124138 : CollatzResearch.WordTrace tailWord_4124138 prefixEnd_4124138 470592239882731227735209 := by
  unfold tailWord_4124138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604917583239961884901267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100279780221973231693070045 37604917583239961884901267)
  ·
    refine ⟨56407376374859942827351901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37604917583239961884901267 56407376374859942827351901)
    ·
      refine ⟨21152766140572478560256963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56407376374859942827351901 21152766140572478560256963)
      ·
        refine ⟨31729149210858717840385445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152766140572478560256963 31729149210858717840385445)
        ·
          refine ⟨5949215477036009595072271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31729149210858717840385445 5949215477036009595072271)
          ·
            refine ⟨8923823215554014392608407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949215477036009595072271 8923823215554014392608407)
            ·
              refine ⟨13385734823331021588912611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923823215554014392608407 13385734823331021588912611)
              ·
                refine ⟨20078602234996532383368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385734823331021588912611 20078602234996532383368917)
                ·
                  refine ⟨470592239882731227735209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20078602234996532383368917 470592239882731227735209)
                  ·
                    rfl

theorem cell22_4124138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_4124138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124138 prefixEnd_4124138 := by exact prefixLift 4124138
  have htrace : WordTrace (prefixWord ++ tailWord_4124138) baseStart_4124138 baseEnd_4124138 := by
    simpa [prefixWord, tailWord_4124138, baseEnd_4124138] using wordTrace_append hprefix tailTrace_4124138
  have hstable : (prefixWord ++ tailWord_4124138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124138).length < 2 ^ (prefixWord ++ tailWord_4124138).sum := by decide
  have hdescent : baseEnd_4124138 < baseStart_4124138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124151 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_4124151 : Nat := 118140960795 + 4124151 * 2 ^ 59
def prefixEnd_4124151 : Nat := 4983230072969 + 3 ^ 40 * 4124151 * 2
def baseEnd_4124151 : Nat := 1411781169813865982630587

theorem tailTrace_4124151 : CollatzResearch.WordTrace tailWord_4124151 prefixEnd_4124151 1411781169813865982630587 := by
  unfold tailWord_4124151
  simp only [CollatzResearch.WordTrace]
  refine ⟨150420144481912750759828307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100280096321275167173218871 150420144481912750759828307)
  ·
    refine ⟨225630216722869126139742461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150420144481912750759828307 225630216722869126139742461)
    ·
      refine ⟨84611331271075922302403423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225630216722869126139742461 84611331271075922302403423)
      ·
        refine ⟨126916996906613883453605135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84611331271075922302403423 126916996906613883453605135)
        ·
          refine ⟨190375495359920825180407703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126916996906613883453605135 190375495359920825180407703)
          ·
            refine ⟨285563243039881237770611555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190375495359920825180407703 285563243039881237770611555)
            ·
              refine ⟨428344864559821856655917333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285563243039881237770611555 428344864559821856655917333)
              ·
                refine ⟨20078665526241649530746125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428344864559821856655917333 20078665526241649530746125)
                ·
                  refine ⟨7529499572340618574029797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20078665526241649530746125 7529499572340618574029797)
                  ·
                    refine ⟨1411781169813865982630587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529499572340618574029797 1411781169813865982630587)
                    ·
                      rfl

theorem cell22_4124151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_4124151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124151 prefixEnd_4124151 := by exact prefixLift 4124151
  have htrace : WordTrace (prefixWord ++ tailWord_4124151) baseStart_4124151 baseEnd_4124151 := by
    simpa [prefixWord, tailWord_4124151, baseEnd_4124151] using wordTrace_append hprefix tailTrace_4124151
  have hstable : (prefixWord ++ tailWord_4124151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124151).length < 2 ^ (prefixWord ++ tailWord_4124151).sum := by decide
  have hdescent : baseEnd_4124151 < baseStart_4124151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124168 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_4124168 : Nat := 118140960795 + 4124168 * 2 ^ 59
def prefixEnd_4124168 : Nat := 4983230072969 + 3 ^ 40 * 4124168 * 2
def baseEnd_4124168 : Nat := 1411786989261283604955535

theorem tailTrace_4124168 : CollatzResearch.WordTrace tailWord_4124168 prefixEnd_4124168 1411786989261283604955535 := by
  unfold tailWord_4124168
  simp only [CollatzResearch.WordTrace]
  refine ⟨75210382261425581331598579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100280509681900775108798105 75210382261425581331598579)
  ·
    refine ⟨112815573392138371997397869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75210382261425581331598579 112815573392138371997397869)
    ·
      refine ⟨42305840022051889499024201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112815573392138371997397869 42305840022051889499024201)
      ·
        refine ⟨31729380016538917124268151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42305840022051889499024201 31729380016538917124268151)
        ·
          refine ⟨47594070024808375686402227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31729380016538917124268151 47594070024808375686402227)
          ·
            refine ⟨71391105037212563529603341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47594070024808375686402227 71391105037212563529603341)
            ·
              refine ⟨26771664388954711323601253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71391105037212563529603341 26771664388954711323601253)
              ·
                refine ⟨5019687072929008373175235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26771664388954711323601253 5019687072929008373175235)
                ·
                  refine ⟨7529530609393512559762853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019687072929008373175235 7529530609393512559762853)
                  ·
                    refine ⟨1411786989261283604955535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529530609393512559762853 1411786989261283604955535)
                    ·
                      rfl

theorem cell22_4124168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_4124168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124168 prefixEnd_4124168 := by exact prefixLift 4124168
  have htrace : WordTrace (prefixWord ++ tailWord_4124168) baseStart_4124168 baseEnd_4124168 := by
    simpa [prefixWord, tailWord_4124168, baseEnd_4124168] using wordTrace_append hprefix tailTrace_4124168
  have hstable : (prefixWord ++ tailWord_4124168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124168).length < 2 ^ (prefixWord ++ tailWord_4124168).sum := by decide
  have hdescent : baseEnd_4124168 < baseStart_4124168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124211 : List Nat := [1, 1, 1, 2, 4, 3, 1, 9]
def baseStart_4124211 : Nat := 118140960795 + 4124211 * 2 ^ 59
def prefixEnd_4124211 : Nat := 4983230072969 + 3 ^ 40 * 4124211 * 2
def baseEnd_4124211 : Nat := 156866856560005091792267

theorem tailTrace_4124211 : CollatzResearch.WordTrace tailWord_4124211 prefixEnd_4124211 156866856560005091792267 := by
  unfold tailWord_4124211
  simp only [CollatzResearch.WordTrace]
  refine ⟨150422332861695381007012487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100281555241130254004674991 150422332861695381007012487)
  ·
    refine ⟨225633499292543071510518731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150422332861695381007012487 225633499292543071510518731)
    ·
      refine ⟨338450248938814607265778097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225633499292543071510518731 338450248938814607265778097)
      ·
        refine ⟨253837686704110955449333573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338450248938814607265778097 253837686704110955449333573)
        ·
          refine ⟨47594566257020804146750045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253837686704110955449333573 47594566257020804146750045)
          ·
            refine ⟨17847962346382801555031267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47594566257020804146750045 17847962346382801555031267)
            ·
              refine ⟨26771943519574202332546901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847962346382801555031267 26771943519574202332546901)
              ·
                refine ⟨156866856560005091792267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26771943519574202332546901 156866856560005091792267)
                ·
                  rfl

theorem cell22_4124211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_4124211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124211 prefixEnd_4124211 := by exact prefixLift 4124211
  have htrace : WordTrace (prefixWord ++ tailWord_4124211) baseStart_4124211 baseEnd_4124211 := by
    simpa [prefixWord, tailWord_4124211, baseEnd_4124211] using wordTrace_append hprefix tailTrace_4124211
  have hstable : (prefixWord ++ tailWord_4124211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124211).length < 2 ^ (prefixWord ++ tailWord_4124211).sum := by decide
  have hdescent : baseEnd_4124211 < baseStart_4124211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124215 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 2, 3]
def baseStart_4124215 : Nat := 118140960795 + 4124215 * 2 ^ 59
def prefixEnd_4124215 : Nat := 4983230072969 + 3 ^ 40 * 4124215 * 2
def baseEnd_4124215 : Nat := 1411803078321791149030391

theorem tailTrace_4124215 : CollatzResearch.WordTrace tailWord_4124215 prefixEnd_4124215 1411803078321791149030391 := by
  unfold tailWord_4124215
  simp only [CollatzResearch.WordTrace]
  refine ⟨150422478753680889690158099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100281652502453926460105399 150422478753680889690158099)
  ·
    refine ⟨225633718130521334535237149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150422478753680889690158099 225633718130521334535237149)
    ·
      refine ⟨84612644298945500450713931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225633718130521334535237149 84612644298945500450713931)
      ·
        refine ⟨126918966448418250676070897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84612644298945500450713931 126918966448418250676070897)
        ·
          refine ⟨95189224836313688007053173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126918966448418250676070897 95189224836313688007053173)
          ·
            refine ⟨8923989828404408250661235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95189224836313688007053173 8923989828404408250661235)
            ·
              refine ⟨13385984742606612375991853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923989828404408250661235 13385984742606612375991853)
              ·
                refine ⟨5019744278477479640996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13385984742606612375991853 5019744278477479640996945)
                ·
                  refine ⟨3764808208858109730747709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019744278477479640996945 3764808208858109730747709)
                  ·
                    refine ⟨1411803078321791149030391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764808208858109730747709 1411803078321791149030391)
                    ·
                      rfl

theorem cell22_4124215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_4124215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124215 prefixEnd_4124215 := by exact prefixLift 4124215
  have htrace : WordTrace (prefixWord ++ tailWord_4124215) baseStart_4124215 baseEnd_4124215 := by
    simpa [prefixWord, tailWord_4124215, baseEnd_4124215] using wordTrace_append hprefix tailTrace_4124215
  have hstable : (prefixWord ++ tailWord_4124215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124215).length < 2 ^ (prefixWord ++ tailWord_4124215).sum := by decide
  have hdescent : baseEnd_4124215 < baseStart_4124215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124277 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4124277 : Nat := 118140960795 + 4124277 * 2 ^ 59
def prefixEnd_4124277 : Nat := 4983230072969 + 3 ^ 40 * 4124277 * 2
def baseEnd_4124277 : Nat := 1411824302188843653980201

theorem tailTrace_4124277 : CollatzResearch.WordTrace tailWord_4124277 prefixEnd_4124277 1411824302188843653980201 := by
  unfold tailWord_4124277
  simp only [CollatzResearch.WordTrace]
  refine ⟨150424740079456274278915085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100283160052970849519276723 150424740079456274278915085)
  ·
    refine ⟨56409277529796102854593157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150424740079456274278915085 56409277529796102854593157)
    ·
      refine ⟨10576739536836769285236217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56409277529796102854593157 10576739536836769285236217)
      ·
        refine ⟨7932554652627576963927163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10576739536836769285236217 7932554652627576963927163)
        ·
          refine ⟨11898831978941365445890745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7932554652627576963927163 11898831978941365445890745)
          ·
            refine ⟨8924123984206024084418059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898831978941365445890745 8924123984206024084418059)
            ·
              refine ⟨13386185976309036126627089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924123984206024084418059 13386185976309036126627089)
              ·
                refine ⟨10039639482231777094970317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13386185976309036126627089 10039639482231777094970317)
                ·
                  refine ⟨3764864805836916410613869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10039639482231777094970317 3764864805836916410613869)
                  ·
                    refine ⟨1411824302188843653980201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764864805836916410613869 1411824302188843653980201)
                    ·
                      rfl

theorem cell22_4124277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4124277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124277 prefixEnd_4124277 := by exact prefixLift 4124277
  have htrace : WordTrace (prefixWord ++ tailWord_4124277) baseStart_4124277 baseEnd_4124277 := by
    simpa [prefixWord, tailWord_4124277, baseEnd_4124277] using wordTrace_append hprefix tailTrace_4124277
  have hstable : (prefixWord ++ tailWord_4124277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124277).length < 2 ^ (prefixWord ++ tailWord_4124277).sum := by decide
  have hdescent : baseEnd_4124277 < baseStart_4124277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124395 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 3, 3]
def baseStart_4124395 : Nat := 118140960795 + 4124395 * 2 ^ 59
def prefixEnd_4124395 : Nat := 4983230072969 + 3 ^ 40 * 4124395 * 2
def baseEnd_4124395 : Nat := 1411864696000330679529839

theorem tailTrace_4124395 : CollatzResearch.WordTrace tailWord_4124395 prefixEnd_4124395 1411864696000330679529839 := by
  unfold tailWord_4124395
  simp only [CollatzResearch.WordTrace]
  refine ⟨150429043893028780431710639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100286029262019186954473759 150429043893028780431710639)
  ·
    refine ⟨225643565839543170647565959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150429043893028780431710639 225643565839543170647565959)
    ·
      refine ⟨338465348759314755971348939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225643565839543170647565959 338465348759314755971348939)
      ·
        refine ⟨507698023138972133957023409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338465348759314755971348939 507698023138972133957023409)
        ·
          refine ⟨380773517354229100467767557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507698023138972133957023409 380773517354229100467767557)
          ·
            refine ⟨71395034503917956337706417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380773517354229100467767557 71395034503917956337706417)
            ·
              refine ⟨53546275877938467253279813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71395034503917956337706417 53546275877938467253279813)
              ·
                refine ⟨10039926727113462609989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53546275877938467253279813 10039926727113462609989965)
                ·
                  refine ⟨3764972522667548478746237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10039926727113462609989965 3764972522667548478746237)
                  ·
                    refine ⟨1411864696000330679529839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764972522667548478746237 1411864696000330679529839)
                    ·
                      rfl

theorem cell22_4124395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].length) (baseStart_4124395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124395 prefixEnd_4124395 := by exact prefixLift 4124395
  have htrace : WordTrace (prefixWord ++ tailWord_4124395) baseStart_4124395 baseEnd_4124395 := by
    simpa [prefixWord, tailWord_4124395, baseEnd_4124395] using wordTrace_append hprefix tailTrace_4124395
  have hstable : (prefixWord ++ tailWord_4124395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124395).length < 2 ^ (prefixWord ++ tailWord_4124395).sum := by decide
  have hdescent : baseEnd_4124395 < baseStart_4124395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124408 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_4124408 : Nat := 118140960795 + 4124408 * 2 ^ 59
def prefixEnd_4124408 : Nat := 4983230072969 + 3 ^ 40 * 4124408 * 2
def baseEnd_4124408 : Nat := 470623048722000992984933

theorem tailTrace_4124408 : CollatzResearch.WordTrace tailWord_4124408 prefixEnd_4124408 470623048722000992984933 := by
  unfold tailWord_4124408
  simp only [CollatzResearch.WordTrace]
  refine ⟨75214759020990841825966939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100286345361321122434622585 75214759020990841825966939)
  ·
    refine ⟨112822138531486262738950409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75214759020990841825966939 112822138531486262738950409)
    ·
      refine ⟨84616603898614697054212807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112822138531486262738950409 84616603898614697054212807)
      ·
        refine ⟨126924905847922045581319211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84616603898614697054212807 126924905847922045581319211)
        ·
          refine ⟨190387358771883068371978817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126924905847922045581319211 190387358771883068371978817)
          ·
            refine ⟨142790519078912301278984113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190387358771883068371978817 142790519078912301278984113)
            ·
              refine ⟨107092889309184225959238085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142790519078912301278984113 107092889309184225959238085)
              ·
                refine ⟨20079916745472042367357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107092889309184225959238085 20079916745472042367357141)
                ·
                  refine ⟨470623048722000992984933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20079916745472042367357141 470623048722000992984933)
                  ·
                    rfl

theorem cell22_4124408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_4124408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124408 prefixEnd_4124408 := by exact prefixLift 4124408
  have htrace : WordTrace (prefixWord ++ tailWord_4124408) baseStart_4124408 baseEnd_4124408 := by
    simpa [prefixWord, tailWord_4124408, baseEnd_4124408] using wordTrace_append hprefix tailTrace_4124408
  have hstable : (prefixWord ++ tailWord_4124408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124408).length < 2 ^ (prefixWord ++ tailWord_4124408).sum := by decide
  have hdescent : baseEnd_4124408 < baseStart_4124408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124472 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_4124472 : Nat := 118140960795 + 4124472 * 2 ^ 59
def prefixEnd_4124472 : Nat := 4983230072969 + 3 ^ 40 * 4124472 * 2
def baseEnd_4124472 : Nat := 1411891054673928145354603

theorem tailTrace_4124472 : CollatzResearch.WordTrace tailWord_4124472 prefixEnd_4124472 1411891054673928145354603 := by
  unfold tailWord_4124472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75215926156874911291131835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100287901542499881721509113 75215926156874911291131835)
  ·
    refine ⟨112823889235312366936697753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75215926156874911291131835 112823889235312366936697753)
    ·
      refine ⟨84617916926484275202523315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112823889235312366936697753 84617916926484275202523315)
      ·
        refine ⟨126926875389726412803784973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84617916926484275202523315 126926875389726412803784973)
        ·
          refine ⟨47597578271147404801419365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126926875389726412803784973 47597578271147404801419365)
          ·
            refine ⟨8924545925840138400266131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47597578271147404801419365 8924545925840138400266131)
            ·
              refine ⟨13386818888760207600399197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924545925840138400266131 13386818888760207600399197)
              ·
                refine ⟨5020057083285077850149699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13386818888760207600399197 5020057083285077850149699)
                ·
                  refine ⟨7530085624927616775224549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020057083285077850149699 7530085624927616775224549)
                  ·
                    refine ⟨1411891054673928145354603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530085624927616775224549 1411891054673928145354603)
                    ·
                      rfl

theorem cell22_4124472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_4124472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124472 prefixEnd_4124472 := by exact prefixLift 4124472
  have htrace : WordTrace (prefixWord ++ tailWord_4124472) baseStart_4124472 baseEnd_4124472 := by
    simpa [prefixWord, tailWord_4124472, baseEnd_4124472] using wordTrace_append hprefix tailTrace_4124472
  have hstable : (prefixWord ++ tailWord_4124472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124472).length < 2 ^ (prefixWord ++ tailWord_4124472).sum := by decide
  have hdescent : baseEnd_4124472 < baseStart_4124472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124487 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 4]
def baseStart_4124487 : Nat := 118140960795 + 4124487 * 2 ^ 59
def prefixEnd_4124487 : Nat := 4983230072969 + 3 ^ 40 * 4124487 * 2
def baseEnd_4124487 : Nat := 470632063160157702076519

theorem tailTrace_4124487 : CollatzResearch.WordTrace tailWord_4124487 prefixEnd_4124487 470632063160157702076519 := by
  unfold tailWord_4124487
  simp only [CollatzResearch.WordTrace]
  refine ⟨150432399408695480144059715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100288266272463653429373143 150432399408695480144059715)
  ·
    refine ⟨225648599113043220216089573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150432399408695480144059715 225648599113043220216089573)
    ·
      refine ⟨42309112333695603790516795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225648599113043220216089573 42309112333695603790516795)
      ·
        refine ⟨63463668500543405685775193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42309112333695603790516795 63463668500543405685775193)
        ·
          refine ⟨47597751375407554264331395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63463668500543405685775193 47597751375407554264331395)
          ·
            refine ⟨71396627063111331396497093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47597751375407554264331395 71396627063111331396497093)
            ·
              refine ⟨13386867574333374636843205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71396627063111331396497093 13386867574333374636843205)
              ·
                refine ⟨2510037670187507744408101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13386867574333374636843205 2510037670187507744408101)
                ·
                  refine ⟨470632063160157702076519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510037670187507744408101 470632063160157702076519)
                  ·
                    rfl

theorem cell22_4124487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 4].length) (baseStart_4124487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124487 prefixEnd_4124487 := by exact prefixLift 4124487
  have htrace : WordTrace (prefixWord ++ tailWord_4124487) baseStart_4124487 baseEnd_4124487 := by
    simpa [prefixWord, tailWord_4124487, baseEnd_4124487] using wordTrace_append hprefix tailTrace_4124487
  have hstable : (prefixWord ++ tailWord_4124487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124487).length < 2 ^ (prefixWord ++ tailWord_4124487).sum := by decide
  have hdescent : baseEnd_4124487 < baseStart_4124487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124622 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_4124622 : Nat := 118140960795 + 4124622 * 2 ^ 59
def prefixEnd_4124622 : Nat := 4983230072969 + 3 ^ 40 * 4124622 * 2
def baseEnd_4124622 : Nat := 470647467579792584701381

theorem tailTrace_4124622 : CollatzResearch.WordTrace tailWord_4124622 prefixEnd_4124622 470647467579792584701381 := by
  unfold tailWord_4124622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18804665407900799775028015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100291548842137598800149413 18804665407900799775028015)
  ·
    refine ⟨28206998111851199662542023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18804665407900799775028015 28206998111851199662542023)
    ·
      refine ⟨42310497167776799493813035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28206998111851199662542023 42310497167776799493813035)
      ·
        refine ⟨63465745751665199240719553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42310497167776799493813035 63465745751665199240719553)
        ·
          refine ⟨47599309313748899430539665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63465745751665199240719553 47599309313748899430539665)
          ·
            refine ⟨35699481985311674572904749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47599309313748899430539665 35699481985311674572904749)
            ·
              refine ⟨13387305744491877964839281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35699481985311674572904749 13387305744491877964839281)
              ·
                refine ⟨10040479308368908473629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13387305744491877964839281 10040479308368908473629461)
                ·
                  refine ⟨470647467579792584701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10040479308368908473629461 470647467579792584701381)
                  ·
                    rfl

theorem cell22_4124622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_4124622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124622 prefixEnd_4124622 := by exact prefixLift 4124622
  have htrace : WordTrace (prefixWord ++ tailWord_4124622) baseStart_4124622 baseEnd_4124622 := by
    simpa [prefixWord, tailWord_4124622, baseEnd_4124622] using wordTrace_append hprefix tailTrace_4124622
  have hstable : (prefixWord ++ tailWord_4124622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124622).length < 2 ^ (prefixWord ++ tailWord_4124622).sum := by decide
  have hdescent : baseEnd_4124622 < baseStart_4124622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124639 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 4]
def baseStart_4124639 : Nat := 118140960795 + 4124639 * 2 ^ 59
def prefixEnd_4124639 : Nat := 4983230072969 + 3 ^ 40 * 4124639 * 2
def baseEnd_4124639 : Nat := 470649407395598458809697

theorem tailTrace_4124639 : CollatzResearch.WordTrace tailWord_4124639 prefixEnd_4124639 470649407395598458809697 := by
  unfold tailWord_4124639
  simp only [CollatzResearch.WordTrace]
  refine ⟨150437943304144810103592971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100291962202763206735728647 150437943304144810103592971)
  ·
    refine ⟨225656914956217215155389457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150437943304144810103592971 225656914956217215155389457)
    ·
      refine ⟨169242686217162911366542093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225656914956217215155389457 169242686217162911366542093)
      ·
        refine ⟨63466007331436091762453285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169242686217162911366542093 63466007331436091762453285)
        ·
          refine ⟨11899876374644267205459991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63466007331436091762453285 11899876374644267205459991)
          ·
            refine ⟨17849814561966400808189987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11899876374644267205459991 17849814561966400808189987)
            ·
              refine ⟨26774721842949601212284981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849814561966400808189987 26774721842949601212284981)
              ·
                refine ⟨2510130172776525113651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26774721842949601212284981 2510130172776525113651717)
                ·
                  refine ⟨470649407395598458809697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510130172776525113651717 470649407395598458809697)
                  ·
                    rfl

theorem cell22_4124639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 4].length) (baseStart_4124639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124639 prefixEnd_4124639 := by exact prefixLift 4124639
  have htrace : WordTrace (prefixWord ++ tailWord_4124639) baseStart_4124639 baseEnd_4124639 := by
    simpa [prefixWord, tailWord_4124639, baseEnd_4124639] using wordTrace_append hprefix tailTrace_4124639
  have hstable : (prefixWord ++ tailWord_4124639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124639).length < 2 ^ (prefixWord ++ tailWord_4124639).sum := by decide
  have hdescent : baseEnd_4124639 < baseStart_4124639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124652 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_4124652 : Nat := 118140960795 + 4124652 * 2 ^ 59
def prefixEnd_4124652 : Nat := 4983230072969 + 3 ^ 40 * 4124652 * 2
def baseEnd_4124652 : Nat := 1411952672352467675854051

theorem tailTrace_4124652 : CollatzResearch.WordTrace tailWord_4124652 prefixEnd_4124652 1411952672352467675854051 := by
  unfold tailWord_4124652
  simp only [CollatzResearch.WordTrace]
  refine ⟨75219208726548856661908105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100292278302065142215877473 75219208726548856661908105)
  ·
    refine ⟨56414406544911642496431079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75219208726548856661908105 56414406544911642496431079)
    ·
      refine ⟨84621609817367463744646619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56414406544911642496431079 84621609817367463744646619)
      ·
        refine ⟨126932414726051195616969929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84621609817367463744646619 126932414726051195616969929)
        ·
          refine ⟨95199311044538396712727447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126932414726051195616969929 95199311044538396712727447)
          ·
            refine ⟨142798966566807595069091171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95199311044538396712727447 142798966566807595069091171)
            ·
              refine ⟨214198449850211392603636757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142798966566807595069091171 214198449850211392603636757)
              ·
                refine ⟨10040552336728659028295473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214198449850211392603636757 10040552336728659028295473)
                ·
                  refine ⟨7530414252546494271221605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10040552336728659028295473 7530414252546494271221605)
                  ·
                    refine ⟨1411952672352467675854051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530414252546494271221605 1411952672352467675854051)
                    ·
                      rfl

theorem cell22_4124652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_4124652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124652 prefixEnd_4124652 := by exact prefixLift 4124652
  have htrace : WordTrace (prefixWord ++ tailWord_4124652) baseStart_4124652 baseEnd_4124652 := by
    simpa [prefixWord, tailWord_4124652, baseEnd_4124652] using wordTrace_append hprefix tailTrace_4124652
  have hstable : (prefixWord ++ tailWord_4124652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124652).length < 2 ^ (prefixWord ++ tailWord_4124652).sum := by decide
  have hdescent : baseEnd_4124652 < baseStart_4124652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124727 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4124727 : Nat := 118140960795 + 4124727 * 2 ^ 59
def prefixEnd_4124727 : Nat := 4983230072969 + 3 ^ 40 * 4124727 * 2
def baseEnd_4124727 : Nat := 1411978346385192480228821

theorem tailTrace_4124727 : CollatzResearch.WordTrace tailWord_4124727 prefixEnd_4124727 1411978346385192480228821 := by
  unfold tailWord_4124727
  simp only [CollatzResearch.WordTrace]
  refine ⟨150441152927826001132796435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100294101951884000755197623 150441152927826001132796435)
  ·
    refine ⟨225661729391739001699194653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150441152927826001132796435 225661729391739001699194653)
    ·
      refine ⟨84623148521902125637197995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225661729391739001699194653 84623148521902125637197995)
      ·
        refine ⟨126934722782853188455796993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84623148521902125637197995 126934722782853188455796993)
        ·
          refine ⟨95201042087139891341847745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126934722782853188455796993 95201042087139891341847745)
          ·
            refine ⟨71400781565354918506385809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95201042087139891341847745 71400781565354918506385809)
            ·
              refine ⟨53550586174016188879789357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71400781565354918506385809 53550586174016188879789357)
              ·
                refine ⟨20081469815256070829921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53550586174016188879789357 20081469815256070829921009)
                ·
                  refine ⟨15061102361442053122440757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081469815256070829921009 15061102361442053122440757)
                  ·
                    refine ⟨1411978346385192480228821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15061102361442053122440757 1411978346385192480228821)
                    ·
                      rfl

theorem cell22_4124727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4124727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124727 prefixEnd_4124727 := by exact prefixLift 4124727
  have htrace : WordTrace (prefixWord ++ tailWord_4124727) baseStart_4124727 baseEnd_4124727 := by
    simpa [prefixWord, tailWord_4124727, baseEnd_4124727] using wordTrace_append hprefix tailTrace_4124727
  have hstable : (prefixWord ++ tailWord_4124727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124727).length < 2 ^ (prefixWord ++ tailWord_4124727).sum := by decide
  have hdescent : baseEnd_4124727 < baseStart_4124727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124759 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 1, 4]
def baseStart_4124759 : Nat := 118140960795 + 4124759 * 2 ^ 59
def prefixEnd_4124759 : Nat := 4983230072969 + 3 ^ 40 * 4124759 * 2
def baseEnd_4124759 : Nat := 1411989300639155063428723

theorem tailTrace_4124759 : CollatzResearch.WordTrace tailWord_4124759 prefixEnd_4124759 1411989300639155063428723 := by
  unfold tailWord_4124759
  simp only [CollatzResearch.WordTrace]
  refine ⟨150442320063710070597961331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100294880042473380398640887 150442320063710070597961331)
  ·
    refine ⟨225663480095565105896941997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150442320063710070597961331 225663480095565105896941997)
    ·
      refine ⟨84623805035836914711353249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225663480095565105896941997 84623805035836914711353249)
      ·
        refine ⟨63467853776877686033514937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84623805035836914711353249 63467853776877686033514937)
        ·
          refine ⟨47600890332658264525136203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63467853776877686033514937 47600890332658264525136203)
          ·
            refine ⟨71401335498987396787704305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47600890332658264525136203 71401335498987396787704305)
            ·
              refine ⟨53551001624240547590778229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71401335498987396787704305 53551001624240547590778229)
              ·
                refine ⟨5020406402272551336635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53551001624240547590778229 5020406402272551336635459)
                ·
                  refine ⟨7530609603408827004953189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020406402272551336635459 7530609603408827004953189)
                  ·
                    refine ⟨1411989300639155063428723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530609603408827004953189 1411989300639155063428723)
                    ·
                      rfl

theorem cell22_4124759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_4124759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124759 prefixEnd_4124759 := by exact prefixLift 4124759
  have htrace : WordTrace (prefixWord ++ tailWord_4124759) baseStart_4124759 baseEnd_4124759 := by
    simpa [prefixWord, tailWord_4124759, baseEnd_4124759] using wordTrace_append hprefix tailTrace_4124759
  have hstable : (prefixWord ++ tailWord_4124759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124759).length < 2 ^ (prefixWord ++ tailWord_4124759).sum := by decide
  have hdescent : baseEnd_4124759 < baseStart_4124759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124804 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4124804 : Nat := 118140960795 + 4124804 * 2 ^ 59
def prefixEnd_4124804 : Nat := 4983230072969 + 3 ^ 40 * 4124804 * 2
def baseEnd_4124804 : Nat := 1412004705058789946053585

theorem tailTrace_4124804 : CollatzResearch.WordTrace tailWord_4124804 prefixEnd_4124804 1412004705058789946053585 := by
  unfold tailWord_4124804
  simp only [CollatzResearch.WordTrace]
  refine ⟨75221980674273521641674733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100295974232364695522232977 75221980674273521641674733)
  ·
    refine ⟨28208242752852570615628025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75221980674273521641674733 28208242752852570615628025)
    ·
      refine ⟨21156182064639427961721019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28208242752852570615628025 21156182064639427961721019)
      ·
        refine ⟨31734273096959141942581529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156182064639427961721019 31734273096959141942581529)
        ·
          refine ⟨23800704822719356456936147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31734273096959141942581529 23800704822719356456936147)
          ·
            refine ⟨35701057234079034685404221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23800704822719356456936147 35701057234079034685404221)
            ·
              refine ⟨13387896462779638007026583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35701057234079034685404221 13387896462779638007026583)
              ·
                refine ⟨20081844694169457010539875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387896462779638007026583 20081844694169457010539875)
                ·
                  refine ⟨30122767041254185515809813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20081844694169457010539875 30122767041254185515809813)
                  ·
                    refine ⟨1412004705058789946053585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30122767041254185515809813 1412004705058789946053585)
                    ·
                      rfl

theorem cell22_4124804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4124804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124804 prefixEnd_4124804 := by exact prefixLift 4124804
  have htrace : WordTrace (prefixWord ++ tailWord_4124804) baseStart_4124804 baseEnd_4124804 := by
    simpa [prefixWord, tailWord_4124804, baseEnd_4124804] using wordTrace_append hprefix tailTrace_4124804
  have hstable : (prefixWord ++ tailWord_4124804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124804).length < 2 ^ (prefixWord ++ tailWord_4124804).sum := by decide
  have hdescent : baseEnd_4124804 < baseStart_4124804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124808 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_4124808 : Nat := 118140960795 + 4124808 * 2 ^ 59
def prefixEnd_4124808 : Nat := 4983230072969 + 3 ^ 40 * 4124808 * 2
def baseEnd_4124808 : Nat := 470668691446845089651191

theorem tailTrace_4124808 : CollatzResearch.WordTrace tailWord_4124808 prefixEnd_4124808 470668691446845089651191 := by
  unfold tailWord_4124808
  simp only [CollatzResearch.WordTrace]
  refine ⟨75222053620266275983247539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100296071493688367977663385 75222053620266275983247539)
  ·
    refine ⟨112833080430399413974871309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75222053620266275983247539 112833080430399413974871309)
    ·
      refine ⟨42312405161399780240576741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112833080430399413974871309 42312405161399780240576741)
      ·
        refine ⟨7933575967762458795108139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42312405161399780240576741 7933575967762458795108139)
        ·
          refine ⟨11900363951643688192662209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933575967762458795108139 11900363951643688192662209)
          ·
            refine ⟨8925272963732766144496657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900363951643688192662209 8925272963732766144496657)
            ·
              refine ⟨6693954722799574608372493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8925272963732766144496657 6693954722799574608372493)
              ·
                refine ⟨2510233021049840478139685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6693954722799574608372493 2510233021049840478139685)
                ·
                  refine ⟨470668691446845089651191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510233021049840478139685 470668691446845089651191)
                  ·
                    rfl

theorem cell22_4124808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_4124808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124808 prefixEnd_4124808 := by exact prefixLift 4124808
  have htrace : WordTrace (prefixWord ++ tailWord_4124808) baseStart_4124808 baseEnd_4124808 := by
    simpa [prefixWord, tailWord_4124808, baseEnd_4124808] using wordTrace_append hprefix tailTrace_4124808
  have hstable : (prefixWord ++ tailWord_4124808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124808).length < 2 ^ (prefixWord ++ tailWord_4124808).sum := by decide
  have hdescent : baseEnd_4124808 < baseStart_4124808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124817 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_4124817 : Nat := 118140960795 + 4124817 * 2 ^ 59
def prefixEnd_4124817 : Nat := 4983230072969 + 3 ^ 40 * 4124817 * 2
def baseEnd_4124817 : Nat := 1412009155224462245478545

theorem tailTrace_4124817 : CollatzResearch.WordTrace tailWord_4124817 prefixEnd_4124817 1412009155224462245478545 := by
  unfold tailWord_4124817
  simp only [CollatzResearch.WordTrace]
  refine ⟨150444435497499946503572705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100296290331666631002381803 150444435497499946503572705)
  ·
    refine ⟨112833326623124959877679529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150444435497499946503572705 112833326623124959877679529)
    ·
      refine ⟨84624994967343719908259647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112833326623124959877679529 84624994967343719908259647)
      ·
        refine ⟨126937492451015579862389471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84624994967343719908259647 126937492451015579862389471)
        ·
          refine ⟨190406238676523369793584207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126937492451015579862389471 190406238676523369793584207)
          ·
            refine ⟨285609358014785054690376311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190406238676523369793584207 285609358014785054690376311)
            ·
              refine ⟨428414037022177582035564467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285609358014785054690376311 428414037022177582035564467)
              ·
                refine ⟨642621055533266373053346701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428414037022177582035564467 642621055533266373053346701)
                ·
                  refine ⟨240982895824974889895005013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642621055533266373053346701 240982895824974889895005013)
                  ·
                    refine ⟨1412009155224462245478545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240982895824974889895005013 1412009155224462245478545)
                    ·
                      rfl

theorem cell22_4124817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_4124817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124817 prefixEnd_4124817 := by exact prefixLift 4124817
  have htrace : WordTrace (prefixWord ++ tailWord_4124817) baseStart_4124817 baseEnd_4124817 := by
    simpa [prefixWord, tailWord_4124817, baseEnd_4124817] using wordTrace_append hprefix tailTrace_4124817
  have hstable : (prefixWord ++ tailWord_4124817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124817).length < 2 ^ (prefixWord ++ tailWord_4124817).sum := by decide
  have hdescent : baseEnd_4124817 < baseStart_4124817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124864 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_4124864 : Nat := 118140960795 + 4124864 * 2 ^ 59
def prefixEnd_4124864 : Nat := 4983230072969 + 3 ^ 40 * 4124864 * 2
def baseEnd_4124864 : Nat := 470675081428323263184467

theorem tailTrace_4124864 : CollatzResearch.WordTrace tailWord_4124864 prefixEnd_4124864 470675081428323263184467 := by
  unfold tailWord_4124864
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223074864164836765266823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100297433152219782353689097 75223074864164836765266823)
  ·
    refine ⟨112834612296247255147900235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75223074864164836765266823 112834612296247255147900235)
    ·
      refine ⟨169251918444370882721850353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112834612296247255147900235 169251918444370882721850353)
      ·
        refine ⟨126938938833278162041387765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169251918444370882721850353 126938938833278162041387765)
        ·
          refine ⟨11900525515619827691380103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126938938833278162041387765 11900525515619827691380103)
          ·
            refine ⟨17850788273429741537070155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900525515619827691380103 17850788273429741537070155)
            ·
              refine ⟨26776182410144612305605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17850788273429741537070155 26776182410144612305605233)
              ·
                refine ⟨20082136807608459229203925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26776182410144612305605233 20082136807608459229203925)
                ·
                  refine ⟨470675081428323263184467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20082136807608459229203925 470675081428323263184467)
                  ·
                    rfl

theorem cell22_4124864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_4124864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124864 prefixEnd_4124864 := by exact prefixLift 4124864
  have htrace : WordTrace (prefixWord ++ tailWord_4124864) baseStart_4124864 baseEnd_4124864 := by
    simpa [prefixWord, tailWord_4124864, baseEnd_4124864] using wordTrace_append hprefix tailTrace_4124864
  have hstable : (prefixWord ++ tailWord_4124864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124864).length < 2 ^ (prefixWord ++ tailWord_4124864).sum := by decide
  have hdescent : baseEnd_4124864 < baseStart_4124864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124885 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_4124885 : Nat := 118140960795 + 4124885 * 2 ^ 59
def prefixEnd_4124885 : Nat := 4983230072969 + 3 ^ 40 * 4124885 * 2
def baseEnd_4124885 : Nat := 1412032433014132734778337

theorem tailTrace_4124885 : CollatzResearch.WordTrace tailWord_4124885 prefixEnd_4124885 1412032433014132734778337 := by
  unfold tailWord_4124885
  simp only [CollatzResearch.WordTrace]
  refine ⟨150446915661253594117048109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100297943774169062744698739 150446915661253594117048109)
  ·
    refine ⟨56417593372970097793893041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150446915661253594117048109 56417593372970097793893041)
    ·
      refine ⟨42313195029727573345419781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56417593372970097793893041 42313195029727573345419781)
      ·
        refine ⟨7933724068073920002266209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42313195029727573345419781 7933724068073920002266209)
        ·
          refine ⟨5950293051055440001699657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7933724068073920002266209 5950293051055440001699657)
          ·
            refine ⟨4462719788291580001274743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950293051055440001699657 4462719788291580001274743)
            ·
              refine ⟨6694079682437370001912115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462719788291580001274743 6694079682437370001912115)
              ·
                refine ⟨10041119523656055002868173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694079682437370001912115 10041119523656055002868173)
                ·
                  refine ⟨3765419821371020626075565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10041119523656055002868173 3765419821371020626075565)
                  ·
                    refine ⟨1412032433014132734778337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3765419821371020626075565 1412032433014132734778337)
                    ·
                      rfl

theorem cell22_4124885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_4124885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124885 prefixEnd_4124885 := by exact prefixLift 4124885
  have htrace : WordTrace (prefixWord ++ tailWord_4124885) baseStart_4124885 baseEnd_4124885 := by
    simpa [prefixWord, tailWord_4124885, baseEnd_4124885] using wordTrace_append hprefix tailTrace_4124885
  have hstable : (prefixWord ++ tailWord_4124885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124885).length < 2 ^ (prefixWord ++ tailWord_4124885).sum := by decide
  have hdescent : baseEnd_4124885 < baseStart_4124885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124911 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_4124911 : Nat := 118140960795 + 4124911 * 2 ^ 59
def prefixEnd_4124911 : Nat := 4983230072969 + 3 ^ 40 * 4124911 * 2
def baseEnd_4124911 : Nat := 1412041333345477333628257

theorem tailTrace_4124911 : CollatzResearch.WordTrace tailWord_4124911 prefixEnd_4124911 1412041333345477333628257 := by
  unfold tailWord_4124911
  simp only [CollatzResearch.WordTrace]
  refine ⟨150447863959159400557494587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100298575972772933704996391 150447863959159400557494587)
  ·
    refine ⟨225671795938739100836241881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150447863959159400557494587 225671795938739100836241881)
    ·
      refine ⟨169253846954054325627181411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225671795938739100836241881 169253846954054325627181411)
      ·
        refine ⟨253880770431081488440772117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169253846954054325627181411 253880770431081488440772117)
        ·
          refine ⟨11900661113956944770661193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253880770431081488440772117 11900661113956944770661193)
          ·
            refine ⟨8925495835467708577995895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900661113956944770661193 8925495835467708577995895)
            ·
              refine ⟨13388243753201562866993843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925495835467708577995895 13388243753201562866993843)
              ·
                refine ⟨20082365629802344300490765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388243753201562866993843 20082365629802344300490765)
                ·
                  refine ⟨7530887111175879112684037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20082365629802344300490765 7530887111175879112684037)
                  ·
                    refine ⟨1412041333345477333628257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530887111175879112684037 1412041333345477333628257)
                    ·
                      rfl

theorem cell22_4124911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_4124911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4124911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4124911 prefixEnd_4124911 := by exact prefixLift 4124911
  have htrace : WordTrace (prefixWord ++ tailWord_4124911) baseStart_4124911 baseEnd_4124911 := by
    simpa [prefixWord, tailWord_4124911, baseEnd_4124911] using wordTrace_append hprefix tailTrace_4124911
  have hstable : (prefixWord ++ tailWord_4124911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124911).length < 2 ^ (prefixWord ++ tailWord_4124911).sum := by decide
  have hdescent : baseEnd_4124911 < baseStart_4124911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125080 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_4125080 : Nat := 118140960795 + 4125080 * 2 ^ 59
def prefixEnd_4125080 : Nat := 4983230072969 + 3 ^ 40 * 4125080 * 2
def baseEnd_4125080 : Nat := 1412099185499217226152739

theorem tailTrace_4125080 : CollatzResearch.WordTrace tailWord_4125080 prefixEnd_4125080 1412099185499217226152739 := by
  unfold tailWord_4125080
  simp only [CollatzResearch.WordTrace]
  refine ⟨75227013947773571210198347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100302685263698094946931129 75227013947773571210198347)
  ·
    refine ⟨112840520921660356815297521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75227013947773571210198347 112840520921660356815297521)
    ·
      refine ⟨84630390691245267611473141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112840520921660356815297521 84630390691245267611473141)
      ·
        refine ⟨7934099127304243838575607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84630390691245267611473141 7934099127304243838575607)
        ·
          refine ⟨11901148690956365757863411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934099127304243838575607 11901148690956365757863411)
          ·
            refine ⟨17851723036434548636795117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901148690956365757863411 17851723036434548636795117)
            ·
              refine ⟨6694396138662955738798169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17851723036434548636795117 6694396138662955738798169)
              ·
                refine ⟨5020797103997216804098627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694396138662955738798169 5020797103997216804098627)
                ·
                  refine ⟨7531195655995825206147941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020797103997216804098627 7531195655995825206147941)
                  ·
                    refine ⟨1412099185499217226152739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7531195655995825206147941 1412099185499217226152739)
                    ·
                      rfl

theorem cell22_4125080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_4125080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125080 prefixEnd_4125080 := by exact prefixLift 4125080
  have htrace : WordTrace (prefixWord ++ tailWord_4125080) baseStart_4125080 baseEnd_4125080 := by
    simpa [prefixWord, tailWord_4125080, baseEnd_4125080] using wordTrace_append hprefix tailTrace_4125080
  have hstable : (prefixWord ++ tailWord_4125080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125080).length < 2 ^ (prefixWord ++ tailWord_4125080).sum := by decide
  have hdescent : baseEnd_4125080 < baseStart_4125080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125140 : List Nat := [2, 4, 1, 2, 2, 2, 3, 6]
def baseStart_4125140 : Nat := 118140960795 + 4125140 * 2 ^ 59
def prefixEnd_4125140 : Nat := 4983230072969 + 3 ^ 40 * 4125140 * 2
def baseEnd_4125140 : Nat := 156902191636155229961395

theorem tailTrace_4125140 : CollatzResearch.WordTrace tailWord_4125140 prefixEnd_4125140 156902191636155229961395 := by
  unfold tailWord_4125140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75228108137664886333790437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100304144183553181778387249 75228108137664886333790437)
  ·
    refine ⟨14105270275812166187585707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75228108137664886333790437 14105270275812166187585707)
    ·
      refine ⟨21157905413718249281378561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14105270275812166187585707 21157905413718249281378561)
      ·
        refine ⟨15868429060288686961033921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21157905413718249281378561 15868429060288686961033921)
        ·
          refine ⟨11901321795216515220775441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15868429060288686961033921 11901321795216515220775441)
          ·
            refine ⟨8925991346412386415581581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11901321795216515220775441 8925991346412386415581581)
            ·
              refine ⟨3347246754904644905843093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8925991346412386415581581 3347246754904644905843093)
              ·
                refine ⟨156902191636155229961395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3347246754904644905843093 156902191636155229961395)
                ·
                  rfl

theorem cell22_4125140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_4125140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125140 prefixEnd_4125140 := by exact prefixLift 4125140
  have htrace : WordTrace (prefixWord ++ tailWord_4125140) baseStart_4125140 baseEnd_4125140 := by
    simpa [prefixWord, tailWord_4125140, baseEnd_4125140] using wordTrace_append hprefix tailTrace_4125140
  have hstable : (prefixWord ++ tailWord_4125140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125140).length < 2 ^ (prefixWord ++ tailWord_4125140).sum := by decide
  have hdescent : baseEnd_4125140 < baseStart_4125140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125223 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4125223 : Nat := 118140960795 + 4125223 * 2 ^ 59
def prefixEnd_4125223 : Nat := 4983230072969 + 3 ^ 40 * 4125223 * 2
def baseEnd_4125223 : Nat := 1412148137321612519827301

theorem tailTrace_4125223 : CollatzResearch.WordTrace tailWord_4125223 prefixEnd_4125223 1412148137321612519827301 := by
  unfold tailWord_4125223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150459243534029077842852323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100306162356019385228568215 150459243534029077842852323)
  ·
    refine ⟨225688865301043616764278485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150459243534029077842852323 225688865301043616764278485)
    ·
      refine ⟨5289582780493209767912777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225688865301043616764278485 5289582780493209767912777)
      ·
        refine ⟨3967187085369907325934583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5289582780493209767912777 3967187085369907325934583)
        ·
          refine ⟨5950780628054860988901875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967187085369907325934583 5950780628054860988901875)
          ·
            refine ⟨8926170942082291483352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950780628054860988901875 8926170942082291483352813)
            ·
              refine ⟨3347314103280859306257305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8926170942082291483352813 3347314103280859306257305)
              ·
                refine ⟨2510485577460644479692979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347314103280859306257305 2510485577460644479692979)
                ·
                  refine ⟨3765728366190966719539469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510485577460644479692979 3765728366190966719539469)
                  ·
                    refine ⟨1412148137321612519827301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3765728366190966719539469 1412148137321612519827301)
                    ·
                      rfl

theorem cell22_4125223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4125223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125223 prefixEnd_4125223 := by exact prefixLift 4125223
  have htrace : WordTrace (prefixWord ++ tailWord_4125223) baseStart_4125223 baseEnd_4125223 := by
    simpa [prefixWord, tailWord_4125223, baseEnd_4125223] using wordTrace_append hprefix tailTrace_4125223
  have hstable : (prefixWord ++ tailWord_4125223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125223).length < 2 ^ (prefixWord ++ tailWord_4125223).sum := by decide
  have hdescent : baseEnd_4125223 < baseStart_4125223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125236 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4125236 : Nat := 118140960795 + 4125236 * 2 ^ 59
def prefixEnd_4125236 : Nat := 4983230072969 + 3 ^ 40 * 4125236 * 2
def baseEnd_4125236 : Nat := 470717529162428273084087

theorem tailTrace_4125236 : CollatzResearch.WordTrace tailWord_4125236 prefixEnd_4125236 470717529162428273084087 := by
  unfold tailWord_4125236
  simp only [CollatzResearch.WordTrace]
  refine ⟨75229858841490990531537781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100306478455321320708717041 75229858841490990531537781)
  ·
    refine ⟨7052799266389780362331667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75229858841490990531537781 7052799266389780362331667)
    ·
      refine ⟨10579198899584670543497501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052799266389780362331667 10579198899584670543497501)
      ·
        refine ⟨3967199587344251453811563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10579198899584670543497501 3967199587344251453811563)
        ·
          refine ⟨5950799381016377180717345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967199587344251453811563 5950799381016377180717345)
          ·
            refine ⟨4463099535762282885538009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950799381016377180717345 4463099535762282885538009)
            ·
              refine ⟨3347324651821712164153507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463099535762282885538009 3347324651821712164153507)
              ·
                refine ⟨5020986977732568246230261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347324651821712164153507 5020986977732568246230261)
                ·
                  refine ⟨470717529162428273084087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5020986977732568246230261 470717529162428273084087)
                  ·
                    rfl

theorem cell22_4125236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4125236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125236 prefixEnd_4125236 := by exact prefixLift 4125236
  have htrace : WordTrace (prefixWord ++ tailWord_4125236) baseStart_4125236 baseEnd_4125236 := by
    simpa [prefixWord, tailWord_4125236, baseEnd_4125236] using wordTrace_append hprefix tailTrace_4125236
  have hstable : (prefixWord ++ tailWord_4125236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125236).length < 2 ^ (prefixWord ++ tailWord_4125236).sum := by decide
  have hdescent : baseEnd_4125236 < baseStart_4125236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125258 : List Nat := [3, 1, 2, 1, 1, 4, 2, 8]
def baseStart_4125258 : Nat := 118140960795 + 4125258 * 2 ^ 59
def prefixEnd_4125258 : Nat := 4983230072969 + 3 ^ 40 * 4125258 * 2
def baseEnd_4125258 : Nat := 156906679837431566133577

theorem tailTrace_4125258 : CollatzResearch.WordTrace tailWord_4125258 prefixEnd_4125258 156906679837431566133577 := by
  unfold tailWord_4125258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37615130022225569705094107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100307013392601519213584285 37615130022225569705094107)
  ·
    refine ⟨56422695033338354557641161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37615130022225569705094107 56422695033338354557641161)
    ·
      refine ⟨42317021275003765918230871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56422695033338354557641161 42317021275003765918230871)
      ·
        refine ⟨63475531912505648877346307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42317021275003765918230871 63475531912505648877346307)
        ·
          refine ⟨95213297868758473316019461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63475531912505648877346307 95213297868758473316019461)
          ·
            refine ⟨17852493350392213746753649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95213297868758473316019461 17852493350392213746753649)
            ·
              refine ⟨13389370012794160310065237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17852493350392213746753649 13389370012794160310065237)
              ·
                refine ⟨156906679837431566133577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13389370012794160310065237 156906679837431566133577)
                ·
                  rfl

theorem cell22_4125258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_4125258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125258 prefixEnd_4125258 := by exact prefixLift 4125258
  have htrace : WordTrace (prefixWord ++ tailWord_4125258) baseStart_4125258 baseEnd_4125258 := by
    simpa [prefixWord, tailWord_4125258, baseEnd_4125258] using wordTrace_append hprefix tailTrace_4125258
  have hstable : (prefixWord ++ tailWord_4125258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125258).length < 2 ^ (prefixWord ++ tailWord_4125258).sum := by decide
  have hdescent : baseEnd_4125258 < baseStart_4125258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125260 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_4125260 : Nat := 118140960795 + 4125260 * 2 ^ 59
def prefixEnd_4125260 : Nat := 4983230072969 + 3 ^ 40 * 4125260 * 2
def baseEnd_4125260 : Nat := 1412160803177756756652187

theorem tailTrace_4125260 : CollatzResearch.WordTrace tailWord_4125260 prefixEnd_4125260 1412160803177756756652187 := by
  unfold tailWord_4125260
  simp only [CollatzResearch.WordTrace]
  refine ⟨75230296517447516580974617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100307062023263355441299489 75230296517447516580974617)
  ·
    refine ⟨56422722388085637435730963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75230296517447516580974617 56422722388085637435730963)
    ·
      refine ⟨84634083582128456153596445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56422722388085637435730963 84634083582128456153596445)
      ·
        refine ⟨31737781343298171057598667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84634083582128456153596445 31737781343298171057598667)
        ·
          refine ⟨47606672014947256586398001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31737781343298171057598667 47606672014947256586398001)
          ·
            refine ⟨35705004011210442439798501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47606672014947256586398001 35705004011210442439798501)
            ·
              refine ⟨6694688252101957957462219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35705004011210442439798501 6694688252101957957462219)
              ·
                refine ⟨10042032378152936936193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694688252101957957462219 10042032378152936936193329)
                ·
                  refine ⟨7531524283614702702144997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10042032378152936936193329 7531524283614702702144997)
                  ·
                    refine ⟨1412160803177756756652187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7531524283614702702144997 1412160803177756756652187)
                    ·
                      rfl

theorem cell22_4125260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_4125260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125260 prefixEnd_4125260 := by exact prefixLift 4125260
  have htrace : WordTrace (prefixWord ++ tailWord_4125260) baseStart_4125260 baseEnd_4125260 := by
    simpa [prefixWord, tailWord_4125260, baseEnd_4125260] using wordTrace_append hprefix tailTrace_4125260
  have hstable : (prefixWord ++ tailWord_4125260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125260).length < 2 ^ (prefixWord ++ tailWord_4125260).sum := by decide
  have hdescent : baseEnd_4125260 < baseStart_4125260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125399 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 4]
def baseStart_4125399 : Nat := 118140960795 + 4125399 * 2 ^ 59
def prefixEnd_4125399 : Nat := 4983230072969 + 3 ^ 40 * 4125399 * 2
def baseEnd_4125399 : Nat := 470736128572802242475587

theorem tailTrace_4125399 : CollatzResearch.WordTrace tailWord_4125399 prefixEnd_4125399 470736128572802242475587 := by
  unfold tailWord_4125399
  simp only [CollatzResearch.WordTrace]
  refine ⟨150465662781391459901259251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100310441854260973267506167 150465662781391459901259251)
  ·
    refine ⟨225698494172087189851888877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150465662781391459901259251 225698494172087189851888877)
    ·
      refine ⟨84636935314532696194458329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225698494172087189851888877 84636935314532696194458329)
      ·
        refine ⟨63477701485899522145843747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84636935314532696194458329 63477701485899522145843747)
        ·
          refine ⟨95216552228849283218765621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63477701485899522145843747 95216552228849283218765621)
          ·
            refine ⟨8926551771454620301759277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95216552228849283218765621 8926551771454620301759277)
            ·
              refine ⟨3347456914295482613159729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8926551771454620301759277 3347456914295482613159729)
              ·
                refine ⟨2510592685721611959869797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347456914295482613159729 2510592685721611959869797)
                ·
                  refine ⟨470736128572802242475587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510592685721611959869797 470736128572802242475587)
                  ·
                    rfl

theorem cell22_4125399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 4].length) (baseStart_4125399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125399 prefixEnd_4125399 := by exact prefixLift 4125399
  have htrace : WordTrace (prefixWord ++ tailWord_4125399) baseStart_4125399 baseEnd_4125399 := by
    simpa [prefixWord, tailWord_4125399, baseEnd_4125399] using wordTrace_append hprefix tailTrace_4125399
  have hstable : (prefixWord ++ tailWord_4125399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125399).length < 2 ^ (prefixWord ++ tailWord_4125399).sum := by decide
  have hdescent : baseEnd_4125399 < baseStart_4125399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125459 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 1, 3]
def baseStart_4125459 : Nat := 118140960795 + 4125459 * 2 ^ 59
def prefixEnd_4125459 : Nat := 4983230072969 + 3 ^ 40 * 4125459 * 2
def baseEnd_4125459 : Nat := 1412228924944586570926577

theorem tailTrace_4125459 : CollatzResearch.WordTrace tailWord_4125459 prefixEnd_4125459 1412228924944586570926577 := by
  unfold tailWord_4125459
  simp only [CollatzResearch.WordTrace]
  refine ⟨150467851161174090148443431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100311900774116060098962287 150467851161174090148443431)
  ·
    refine ⟨225701776741761135222665147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150467851161174090148443431 225701776741761135222665147)
    ·
      refine ⟨338552665112641702833997721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225701776741761135222665147 338552665112641702833997721)
      ·
        refine ⟨253914498834481277125498291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338552665112641702833997721 253914498834481277125498291)
        ·
          refine ⟨380871748251721915688247437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253914498834481277125498291 380871748251721915688247437)
          ·
            refine ⟨142826905594395718383092789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380871748251721915688247437 142826905594395718383092789)
            ·
              refine ⟨13390022399474598598414949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142826905594395718383092789 13390022399474598598414949)
              ·
                refine ⟨2510629199901487237202803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13390022399474598598414949 2510629199901487237202803)
                ·
                  refine ⟨3765943799852230855804205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510629199901487237202803 3765943799852230855804205)
                  ·
                    refine ⟨1412228924944586570926577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3765943799852230855804205 1412228924944586570926577)
                    ·
                      rfl

theorem cell22_4125459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 3].length) (baseStart_4125459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125459 prefixEnd_4125459 := by exact prefixLift 4125459
  have htrace : WordTrace (prefixWord ++ tailWord_4125459) baseStart_4125459 baseEnd_4125459 := by
    simpa [prefixWord, tailWord_4125459, baseEnd_4125459] using wordTrace_append hprefix tailTrace_4125459
  have hstable : (prefixWord ++ tailWord_4125459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125459).length < 2 ^ (prefixWord ++ tailWord_4125459).sum := by decide
  have hdescent : baseEnd_4125459 < baseStart_4125459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125472 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_4125472 : Nat := 118140960795 + 4125472 * 2 ^ 59
def prefixEnd_4125472 : Nat := 4983230072969 + 3 ^ 40 * 4125472 * 2
def baseEnd_4125472 : Nat := 470744458370086290117179

theorem tailTrace_4125472 : CollatzResearch.WordTrace tailWord_4125472 prefixEnd_4125472 470744458370086290117179 := by
  unfold tailWord_4125472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75234162655063496684333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100312216873417995579111113 75234162655063496684333335)
  ·
    refine ⟨112851243982595245026500003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75234162655063496684333335 112851243982595245026500003)
    ·
      refine ⟨169276865973892867539750005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112851243982595245026500003 169276865973892867539750005)
      ·
        refine ⟨15869706185052456331851563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169276865973892867539750005 15869706185052456331851563)
        ·
          refine ⟨23804559277578684497777345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15869706185052456331851563 23804559277578684497777345)
          ·
            refine ⟨17853419458184013373333009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23804559277578684497777345 17853419458184013373333009)
            ·
              refine ⟨13390064593638010029999757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853419458184013373333009 13390064593638010029999757)
              ·
                refine ⟨5021274222614253761249909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13390064593638010029999757 5021274222614253761249909)
                ·
                  refine ⟨470744458370086290117179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021274222614253761249909 470744458370086290117179)
                  ·
                    rfl

theorem cell22_4125472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_4125472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125472 prefixEnd_4125472 := by exact prefixLift 4125472
  have htrace : WordTrace (prefixWord ++ tailWord_4125472) baseStart_4125472 baseEnd_4125472 := by
    simpa [prefixWord, tailWord_4125472, baseEnd_4125472] using wordTrace_append hprefix tailTrace_4125472
  have hstable : (prefixWord ++ tailWord_4125472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125472).length < 2 ^ (prefixWord ++ tailWord_4125472).sum := by decide
  have hdescent : baseEnd_4125472 < baseStart_4125472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125500 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_4125500 : Nat := 118140960795 + 4125500 * 2 ^ 59
def prefixEnd_4125500 : Nat := 4983230072969 + 3 ^ 40 * 4125500 * 2
def baseEnd_4125500 : Nat := 470747653360825376883817

theorem tailTrace_4125500 : CollatzResearch.WordTrace tailWord_4125500 prefixEnd_4125500 470747653360825376883817 := by
  unfold tailWord_4125500
  simp only [CollatzResearch.WordTrace]
  refine ⟨75234673277012777075342977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100312897702683702767123969 75234673277012777075342977)
  ·
    refine ⟨56426004957759582806507233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75234673277012777075342977 56426004957759582806507233)
    ·
      refine ⟨42319503718319687104880425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56426004957759582806507233 42319503718319687104880425)
      ·
        refine ⟨31739627788739765328660319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42319503718319687104880425 31739627788739765328660319)
        ·
          refine ⟨47609441683109647992990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31739627788739765328660319 47609441683109647992990479)
          ·
            refine ⟨71414162524664471989485719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47609441683109647992990479 71414162524664471989485719)
            ·
              refine ⟨107121243786996707984228579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71414162524664471989485719 107121243786996707984228579)
              ·
                refine ⟨160681865680495061976342869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107121243786996707984228579 160681865680495061976342869)
                ·
                  refine ⟨470747653360825376883817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 160681865680495061976342869 470747653360825376883817)
                  ·
                    rfl

theorem cell22_4125500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_4125500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125500 prefixEnd_4125500 := by exact prefixLift 4125500
  have htrace : WordTrace (prefixWord ++ tailWord_4125500) baseStart_4125500 baseEnd_4125500 := by
    simpa [prefixWord, tailWord_4125500, baseEnd_4125500] using wordTrace_append hprefix tailTrace_4125500
  have hstable : (prefixWord ++ tailWord_4125500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125500).length < 2 ^ (prefixWord ++ tailWord_4125500).sum := by decide
  have hdescent : baseEnd_4125500 < baseStart_4125500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125624 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_4125624 : Nat := 118140960795 + 4125624 * 2 ^ 59
def prefixEnd_4125624 : Nat := 4983230072969 + 3 ^ 40 * 4125624 * 2
def baseEnd_4125624 : Nat := 470761802605527046850357

theorem tailTrace_4125624 : CollatzResearch.WordTrace tailWord_4125624 prefixEnd_4125624 470761802605527046850357 := by
  unfold tailWord_4125624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75236934602788161664099963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100315912803717548885466617 75236934602788161664099963)
  ·
    refine ⟨112855401904182242496149945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75236934602788161664099963 112855401904182242496149945)
    ·
      refine ⟨84641551428136681872112459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112855401904182242496149945 84641551428136681872112459)
      ·
        refine ⟨126962327142205022808168689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84641551428136681872112459 126962327142205022808168689)
        ·
          refine ⟨95221745356653767106126517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126962327142205022808168689 95221745356653767106126517)
          ·
            refine ⟨8927038627186290666199361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95221745356653767106126517 8927038627186290666199361)
            ·
              refine ⟨6695278970389717999649521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8927038627186290666199361 6695278970389717999649521)
              ·
                refine ⟨5021459227792288499737141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6695278970389717999649521 5021459227792288499737141)
                ·
                  refine ⟨470761802605527046850357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021459227792288499737141 470761802605527046850357)
                  ·
                    rfl

theorem cell22_4125624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_4125624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125624 prefixEnd_4125624 := by exact prefixLift 4125624
  have htrace : WordTrace (prefixWord ++ tailWord_4125624) baseStart_4125624 baseEnd_4125624 := by
    simpa [prefixWord, tailWord_4125624, baseEnd_4125624] using wordTrace_append hprefix tailTrace_4125624
  have hstable : (prefixWord ++ tailWord_4125624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125624).length < 2 ^ (prefixWord ++ tailWord_4125624).sum := by decide
  have hdescent : baseEnd_4125624 < baseStart_4125624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125671 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4125671 : Nat := 118140960795 + 4125671 * 2 ^ 59
def prefixEnd_4125671 : Nat := 4983230072969 + 3 ^ 40 * 4125671 * 2
def baseEnd_4125671 : Nat := 1412301496877088684625927

theorem tailTrace_4125671 : CollatzResearch.WordTrace tailWord_4125671 prefixEnd_4125671 1412301496877088684625927 := by
  unfold tailWord_4125671
  simp only [CollatzResearch.WordTrace]
  refine ⟨150475583436406050355160867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100317055624270700236773911 150475583436406050355160867)
  ·
    refine ⟨225713375154609075532741301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150475583436406050355160867 225713375154609075532741301)
    ·
      refine ⟨21160628920744600831194497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225713375154609075532741301 21160628920744600831194497)
      ·
        refine ⟨15870471690558450623395873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21160628920744600831194497 15870471690558450623395873)
        ·
          refine ⟨11902853767918837967546905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15870471690558450623395873 11902853767918837967546905)
          ·
            refine ⟨8927140325939128475660179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11902853767918837967546905 8927140325939128475660179)
            ·
              refine ⟨13390710488908692713490269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927140325939128475660179 13390710488908692713490269)
              ·
                refine ⟨5021516433340759767558851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13390710488908692713490269 5021516433340759767558851)
                ·
                  refine ⟨7532274650011139651338277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021516433340759767558851 7532274650011139651338277)
                  ·
                    refine ⟨1412301496877088684625927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532274650011139651338277 1412301496877088684625927)
                    ·
                      rfl

theorem cell22_4125671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4125671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125671 prefixEnd_4125671 := by exact prefixLift 4125671
  have htrace : WordTrace (prefixWord ++ tailWord_4125671) baseStart_4125671 baseEnd_4125671 := by
    simpa [prefixWord, tailWord_4125671, baseEnd_4125671] using wordTrace_append hprefix tailTrace_4125671
  have hstable : (prefixWord ++ tailWord_4125671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125671).length < 2 ^ (prefixWord ++ tailWord_4125671).sum := by decide
  have hdescent : baseEnd_4125671 < baseStart_4125671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125686 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4125686 : Nat := 118140960795 + 4125686 * 2 ^ 59
def prefixEnd_4125686 : Nat := 4983230072969 + 3 ^ 40 * 4125686 * 2
def baseEnd_4125686 : Nat := 470768877227877881833627

theorem tailTrace_4125686 : CollatzResearch.WordTrace tailWord_4125686 prefixEnd_4125686 470768877227877881833627 := by
  unfold tailWord_4125686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404758158209481744809807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100317420354234471944637941 9404758158209481744809807)
  ·
    refine ⟨14107137237314222617214711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404758158209481744809807 14107137237314222617214711)
    ·
      refine ⟨21160705855971333925822067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107137237314222617214711 21160705855971333925822067)
      ·
        refine ⟨31741058783957000888733101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21160705855971333925822067 31741058783957000888733101)
        ·
          refine ⟨11902897043983875333274913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31741058783957000888733101 11902897043983875333274913)
          ·
            refine ⟨8927172782987906499956185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11902897043983875333274913 8927172782987906499956185)
            ·
              refine ⟨6695379587240929874967139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8927172782987906499956185 6695379587240929874967139)
              ·
                refine ⟨10043069380861394812450709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695379587240929874967139 10043069380861394812450709)
                ·
                  refine ⟨470768877227877881833627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10043069380861394812450709 470768877227877881833627)
                  ·
                    rfl

theorem cell22_4125686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4125686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125686 prefixEnd_4125686 := by exact prefixLift 4125686
  have htrace : WordTrace (prefixWord ++ tailWord_4125686) baseStart_4125686 baseEnd_4125686 := by
    simpa [prefixWord, tailWord_4125686, baseEnd_4125686] using wordTrace_append hprefix tailTrace_4125686
  have hstable : (prefixWord ++ tailWord_4125686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125686).length < 2 ^ (prefixWord ++ tailWord_4125686).sum := by decide
  have hdescent : baseEnd_4125686 < baseStart_4125686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125804 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_4125804 : Nat := 118140960795 + 4125804 * 2 ^ 59
def prefixEnd_4125804 : Nat := 4983230072969 + 3 ^ 40 * 4125804 * 2
def baseEnd_4125804 : Nat := 470782341831706890350173

theorem tailTrace_4125804 : CollatzResearch.WordTrace tailWord_4125804 prefixEnd_4125804 470782341831706890350173 := by
  unfold tailWord_4125804
  simp only [CollatzResearch.WordTrace]
  refine ⟨75240217172462107034876233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100320289563282809379834977 75240217172462107034876233)
  ·
    refine ⟨56430162879346580276157175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75240217172462107034876233 56430162879346580276157175)
    ·
      refine ⟨84645244319019870414235763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56430162879346580276157175 84645244319019870414235763)
      ·
        refine ⟨126967866478529805621353645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84645244319019870414235763 126967866478529805621353645)
        ·
          refine ⟨47612949929448677108007617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126967866478529805621353645 47612949929448677108007617)
          ·
            refine ⟨35709712447086507831005713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47612949929448677108007617 35709712447086507831005713)
            ·
              refine ⟨26782284335314880873254285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35709712447086507831005713 26782284335314880873254285)
              ·
                refine ⟨10043356625743080327470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26782284335314880873254285 10043356625743080327470357)
                ·
                  refine ⟨470782341831706890350173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10043356625743080327470357 470782341831706890350173)
                  ·
                    rfl

theorem cell22_4125804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_4125804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125804 prefixEnd_4125804 := by exact prefixLift 4125804
  have htrace : WordTrace (prefixWord ++ tailWord_4125804) baseStart_4125804 baseEnd_4125804 := by
    simpa [prefixWord, tailWord_4125804, baseEnd_4125804] using wordTrace_append hprefix tailTrace_4125804
  have hstable : (prefixWord ++ tailWord_4125804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125804).length < 2 ^ (prefixWord ++ tailWord_4125804).sum := by decide
  have hdescent : baseEnd_4125804 < baseStart_4125804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125806 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_4125806 : Nat := 118140960795 + 4125806 * 2 ^ 59
def prefixEnd_4125806 : Nat := 4983230072969 + 3 ^ 40 * 4125806 * 2
def baseEnd_4125806 : Nat := 1412347710135993332500513

theorem tailTrace_4125806 : CollatzResearch.WordTrace tailWord_4125806 prefixEnd_4125806 1412347710135993332500513 := by
  unfold tailWord_4125806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810063411364621051415659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100320338193944645607550181 18810063411364621051415659)
  ·
    refine ⟨28215095117046931577123489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18810063411364621051415659 28215095117046931577123489)
    ·
      refine ⟨21161321337785198682842617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28215095117046931577123489 21161321337785198682842617)
      ·
        refine ⟨15870991003338899012131963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21161321337785198682842617 15870991003338899012131963)
        ·
          refine ⟨23806486505008348518197945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870991003338899012131963 23806486505008348518197945)
          ·
            refine ⟨17854864878756261388648459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23806486505008348518197945 17854864878756261388648459)
            ·
              refine ⟨26782297318134392082972689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854864878756261388648459 26782297318134392082972689)
              ·
                refine ⟨20086722988600794062229517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26782297318134392082972689 20086722988600794062229517)
                ·
                  refine ⟨7532521120725297773336069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20086722988600794062229517 7532521120725297773336069)
                  ·
                    refine ⟨1412347710135993332500513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532521120725297773336069 1412347710135993332500513)
                    ·
                      rfl

theorem cell22_4125806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_4125806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125806 prefixEnd_4125806 := by exact prefixLift 4125806
  have htrace : WordTrace (prefixWord ++ tailWord_4125806) baseStart_4125806 baseEnd_4125806 := by
    simpa [prefixWord, tailWord_4125806, baseEnd_4125806] using wordTrace_append hprefix tailTrace_4125806
  have hstable : (prefixWord ++ tailWord_4125806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125806).length < 2 ^ (prefixWord ++ tailWord_4125806).sum := by decide
  have hdescent : baseEnd_4125806 < baseStart_4125806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125838 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4125838 : Nat := 118140960795 + 4125838 * 2 ^ 59
def prefixEnd_4125838 : Nat := 4983230072969 + 3 ^ 40 * 4125838 * 2
def baseEnd_4125838 : Nat := 470786221463318638566805

theorem tailTrace_4125838 : CollatzResearch.WordTrace tailWord_4125838 prefixEnd_4125838 470786221463318638566805 := by
  unfold tailWord_4125838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18810209303350129734561271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100321116284534025250993445 18810209303350129734561271)
  ·
    refine ⟨28215313955025194601841907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18810209303350129734561271 28215313955025194601841907)
    ·
      refine ⟨42322970932537791902762861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28215313955025194601841907 42322970932537791902762861)
      ·
        refine ⟨15871114099701671963536073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42322970932537791902762861 15871114099701671963536073)
        ·
          refine ⟨11903335574776253972652055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15871114099701671963536073 11903335574776253972652055)
          ·
            refine ⟨17855003362164380958978083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11903335574776253972652055 17855003362164380958978083)
            ·
              refine ⟨26782505043246571438467125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17855003362164380958978083 26782505043246571438467125)
              ·
                refine ⟨2510859847804366072356293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26782505043246571438467125 2510859847804366072356293)
                ·
                  refine ⟨470786221463318638566805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510859847804366072356293 470786221463318638566805)
                  ·
                    rfl

theorem cell22_4125838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4125838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125838 prefixEnd_4125838 := by exact prefixLift 4125838
  have htrace : WordTrace (prefixWord ++ tailWord_4125838) baseStart_4125838 baseEnd_4125838 := by
    simpa [prefixWord, tailWord_4125838, baseEnd_4125838] using wordTrace_append hprefix tailTrace_4125838
  have hstable : (prefixWord ++ tailWord_4125838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125838).length < 2 ^ (prefixWord ++ tailWord_4125838).sum := by decide
  have hdescent : baseEnd_4125838 < baseStart_4125838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4125988 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4125988 : Nat := 118140960795 + 4125988 * 2 ^ 59
def prefixEnd_4125988 : Nat := 4983230072969 + 3 ^ 40 * 4125988 * 2
def baseEnd_4125988 : Nat := 1412410012455405524449955

theorem tailTrace_4125988 : CollatzResearch.WordTrace tailWord_4125988 prefixEnd_4125988 1412410012455405524449955 := by
  unfold tailWord_4125988
  simp only [CollatzResearch.WordTrace]
  refine ⟨75243572688128806747225309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100324763584171742329633745 75243572688128806747225309)
  ·
    refine ⟨28216339758048302530209491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75243572688128806747225309 28216339758048302530209491)
    ·
      refine ⟨42324509637072453795314237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28216339758048302530209491 42324509637072453795314237)
      ·
        refine ⟨15871691113902170173242839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42324509637072453795314237 15871691113902170173242839)
        ·
          refine ⟨23807536670853255259864259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15871691113902170173242839 23807536670853255259864259)
          ·
            refine ⟨35711305006279882889796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23807536670853255259864259 35711305006279882889796389)
            ·
              refine ⟨6695869688677478041836823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35711305006279882889796389 6695869688677478041836823)
              ·
                refine ⟨10043804533016217062755235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695869688677478041836823 10043804533016217062755235)
                ·
                  refine ⟨15065706799524325594132853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043804533016217062755235 15065706799524325594132853)
                  ·
                    refine ⟨1412410012455405524449955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15065706799524325594132853 1412410012455405524449955)
                    ·
                      rfl

theorem cell22_4125988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4125988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4125988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4125988 prefixEnd_4125988 := by exact prefixLift 4125988
  have htrace : WordTrace (prefixWord ++ tailWord_4125988) baseStart_4125988 baseEnd_4125988 := by
    simpa [prefixWord, tailWord_4125988, baseEnd_4125988] using wordTrace_append hprefix tailTrace_4125988
  have hstable : (prefixWord ++ tailWord_4125988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4125988).length < 2 ^ (prefixWord ++ tailWord_4125988).sum := by decide
  have hdescent : baseEnd_4125988 < baseStart_4125988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4125988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126003 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_4126003 : Nat := 118140960795 + 4126003 * 2 ^ 59
def prefixEnd_4126003 : Nat := 4983230072969 + 3 ^ 40 * 4126003 * 2
def baseEnd_4126003 : Nat := 1412415147261950485324909

theorem tailTrace_4126003 : CollatzResearch.WordTrace tailWord_4126003 prefixEnd_4126003 1412415147261950485324909 := by
  unfold tailWord_4126003
  simp only [CollatzResearch.WordTrace]
  refine ⟨150487692471203271056246663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100325128314135514037497775 150487692471203271056246663)
  ·
    refine ⟨225731538706804906584369995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150487692471203271056246663 225731538706804906584369995)
    ·
      refine ⟨338597308060207359876554993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225731538706804906584369995 338597308060207359876554993)
      ·
        refine ⟨253947981045155519907416245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338597308060207359876554993 253947981045155519907416245)
        ·
          refine ⟨23807623222983329991320273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253947981045155519907416245 23807623222983329991320273)
          ·
            refine ⟨17855717417237497493490205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23807623222983329991320273 17855717417237497493490205)
            ·
              refine ⟨6695894031464061560058827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17855717417237497493490205 6695894031464061560058827)
              ·
                refine ⟨10043841047196092340088241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695894031464061560058827 10043841047196092340088241)
                ·
                  refine ⟨7532880785397069255066181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043841047196092340088241 7532880785397069255066181)
                  ·
                    refine ⟨1412415147261950485324909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532880785397069255066181 1412415147261950485324909)
                    ·
                      rfl

theorem cell22_4126003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_4126003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126003 prefixEnd_4126003 := by exact prefixLift 4126003
  have htrace : WordTrace (prefixWord ++ tailWord_4126003) baseStart_4126003 baseEnd_4126003 := by
    simpa [prefixWord, tailWord_4126003, baseEnd_4126003] using wordTrace_append hprefix tailTrace_4126003
  have hstable : (prefixWord ++ tailWord_4126003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126003).length < 2 ^ (prefixWord ++ tailWord_4126003).sum := by decide
  have hdescent : baseEnd_4126003 < baseStart_4126003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126009 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_4126009 : Nat := 118140960795 + 4126009 * 2 ^ 59
def prefixEnd_4126009 : Nat := 4983230072969 + 3 ^ 40 * 4126009 * 2
def baseEnd_4126009 : Nat := 1412417201184568469674891

theorem tailTrace_4126009 : CollatzResearch.WordTrace tailWord_4126009 prefixEnd_4126009 1412417201184568469674891 := by
  unfold tailWord_4126009
  simp only [CollatzResearch.WordTrace]
  refine ⟨150487911309181534080965081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100325274206121022720643387 150487911309181534080965081)
  ·
    refine ⟨112865933481886150560723811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150487911309181534080965081 112865933481886150560723811)
    ·
      refine ⟨169298900222829225841085717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112865933481886150560723811 169298900222829225841085717)
      ·
        refine ⟨7935885947945119961300893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169298900222829225841085717 7935885947945119961300893)
        ·
          refine ⟨2975957230479419985487835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7935885947945119961300893 2975957230479419985487835)
          ·
            refine ⟨4463935845719129978231753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975957230479419985487835 4463935845719129978231753)
            ·
              refine ⟨3347951884289347483673815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463935845719129978231753 3347951884289347483673815)
              ·
                refine ⟨5021927826434021225510723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347951884289347483673815 5021927826434021225510723)
                ·
                  refine ⟨7532891739651031838266085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021927826434021225510723 7532891739651031838266085)
                  ·
                    refine ⟨1412417201184568469674891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532891739651031838266085 1412417201184568469674891)
                    ·
                      rfl

theorem cell22_4126009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_4126009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126009 prefixEnd_4126009 := by exact prefixLift 4126009
  have htrace : WordTrace (prefixWord ++ tailWord_4126009) baseStart_4126009 baseEnd_4126009 := by
    simpa [prefixWord, tailWord_4126009, baseEnd_4126009] using wordTrace_append hprefix tailTrace_4126009
  have hstable : (prefixWord ++ tailWord_4126009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126009).length < 2 ^ (prefixWord ++ tailWord_4126009).sum := by decide
  have hdescent : baseEnd_4126009 < baseStart_4126009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126050 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4126050 : Nat := 118140960795 + 4126050 * 2 ^ 59
def prefixEnd_4126050 : Nat := 4983230072969 + 3 ^ 40 * 4126050 * 2
def baseEnd_4126050 : Nat := 1412431236322458029399765

theorem tailTrace_4126050 : CollatzResearch.WordTrace tailWord_4126050 prefixEnd_4126050 1412431236322458029399765 := by
  unfold tailWord_4126050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37622351675508249520801901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100326271134688665388805069 37622351675508249520801901)
  ·
    refine ⟨14108381878315593570300713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37622351675508249520801901 14108381878315593570300713)
    ·
      refine ⟨10581286408736695177725535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14108381878315593570300713 10581286408736695177725535)
      ·
        refine ⟨15871929613105042766588303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581286408736695177725535 15871929613105042766588303)
        ·
          refine ⟨23807894419657564149882455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15871929613105042766588303 23807894419657564149882455)
          ·
            refine ⟨35711841629486346224823683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23807894419657564149882455 35711841629486346224823683)
            ·
              refine ⟨53567762444229519337235525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35711841629486346224823683 53567762444229519337235525)
              ·
                refine ⟨10043955458293034875731661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53567762444229519337235525 10043955458293034875731661)
                ·
                  refine ⟨3766483296859888078399373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10043955458293034875731661 3766483296859888078399373)
                  ·
                    refine ⟨1412431236322458029399765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766483296859888078399373 1412431236322458029399765)
                    ·
                      rfl

theorem cell22_4126050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4126050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126050 prefixEnd_4126050 := by exact prefixLift 4126050
  have htrace : WordTrace (prefixWord ++ tailWord_4126050) baseStart_4126050 baseEnd_4126050 := by
    simpa [prefixWord, tailWord_4126050, baseEnd_4126050] using wordTrace_append hprefix tailTrace_4126050
  have hstable : (prefixWord ++ tailWord_4126050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126050).length < 2 ^ (prefixWord ++ tailWord_4126050).sum := by decide
  have hdescent : baseEnd_4126050 < baseStart_4126050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126084 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4126084 : Nat := 118140960795 + 4126084 * 2 ^ 59
def prefixEnd_4126084 : Nat := 4983230072969 + 3 ^ 40 * 4126084 * 2
def baseEnd_4126084 : Nat := 1412442875217293274049661

theorem tailTrace_4126084 : CollatzResearch.WordTrace tailWord_4126084 prefixEnd_4126084 1412442875217293274049661 := by
  unfold tailWord_4126084
  simp only [CollatzResearch.WordTrace]
  refine ⟨75245323391954910944972653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100327097855939881259963537 75245323391954910944972653)
  ·
    refine ⟨28216996271983091604364745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75245323391954910944972653 28216996271983091604364745)
    ·
      refine ⟨21162747203987318703273559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28216996271983091604364745 21162747203987318703273559)
      ·
        refine ⟨31744120805980978054910339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21162747203987318703273559 31744120805980978054910339)
        ·
          refine ⟨47616181208971467082365509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31744120805980978054910339 47616181208971467082365509)
          ·
            refine ⟨8928033976682150077943533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47616181208971467082365509 8928033976682150077943533)
            ·
              refine ⟨3348012741255806279228825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928033976682150077943533 3348012741255806279228825)
              ·
                refine ⟨2511009555941854709421619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348012741255806279228825 2511009555941854709421619)
                ·
                  refine ⟨3766514333912782064132429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511009555941854709421619 3766514333912782064132429)
                  ·
                    refine ⟨1412442875217293274049661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766514333912782064132429 1412442875217293274049661)
                    ·
                      rfl

theorem cell22_4126084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4126084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126084 prefixEnd_4126084 := by exact prefixLift 4126084
  have htrace : WordTrace (prefixWord ++ tailWord_4126084) baseStart_4126084 baseEnd_4126084 := by
    simpa [prefixWord, tailWord_4126084, baseEnd_4126084] using wordTrace_append hprefix tailTrace_4126084
  have hstable : (prefixWord ++ tailWord_4126084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126084).length < 2 ^ (prefixWord ++ tailWord_4126084).sum := by decide
  have hdescent : baseEnd_4126084 < baseStart_4126084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126146 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4126146 : Nat := 118140960795 + 4126146 * 2 ^ 59
def prefixEnd_4126146 : Nat := 4983230072969 + 3 ^ 40 * 4126146 * 2
def baseEnd_4126146 : Nat := 1412464099084345778999471

theorem tailTrace_4126146 : CollatzResearch.WordTrace tailWord_4126146 prefixEnd_4126146 1412464099084345778999471 := by
  unfold tailWord_4126146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623227027421301619675573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100328605406456804319134861 37623227027421301619675573)
  ·
    refine ⟨3527177533820747026844585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37623227027421301619675573 3527177533820747026844585)
    ·
      refine ⟨2645383150365560270133439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527177533820747026844585 2645383150365560270133439)
      ·
        refine ⟨3968074725548340405200159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645383150365560270133439 3968074725548340405200159)
        ·
          refine ⟨5952112088322510607800239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968074725548340405200159 5952112088322510607800239)
          ·
            refine ⟨8928168132483765911700359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952112088322510607800239 8928168132483765911700359)
            ·
              refine ⟨13392252198725648867550539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928168132483765911700359 13392252198725648867550539)
              ·
                refine ⟨20088378298088473301325809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392252198725648867550539 20088378298088473301325809)
                ·
                  refine ⟨15066283723566354975994357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20088378298088473301325809 15066283723566354975994357)
                  ·
                    refine ⟨1412464099084345778999471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15066283723566354975994357 1412464099084345778999471)
                    ·
                      rfl

theorem cell22_4126146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4126146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126146 prefixEnd_4126146 := by exact prefixLift 4126146
  have htrace : WordTrace (prefixWord ++ tailWord_4126146) baseStart_4126146 baseEnd_4126146 := by
    simpa [prefixWord, tailWord_4126146, baseEnd_4126146] using wordTrace_append hprefix tailTrace_4126146
  have hstable : (prefixWord ++ tailWord_4126146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126146).length < 2 ^ (prefixWord ++ tailWord_4126146).sum := by decide
  have hdescent : baseEnd_4126146 < baseStart_4126146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126170 : List Nat := [3, 1, 1, 2, 3, 3, 3, 6]
def baseStart_4126170 : Nat := 118140960795 + 4126170 * 2 ^ 59
def prefixEnd_4126170 : Nat := 4983230072969 + 3 ^ 40 * 4126170 * 2
def baseEnd_4126170 : Nat := 156941368308313079599933

theorem tailTrace_4126170 : CollatzResearch.WordTrace tailWord_4126170 prefixEnd_4126170 156941368308313079599933 := by
  unfold tailWord_4126170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623445865399564644393991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100329188974398839051717309 37623445865399564644393991)
  ·
    refine ⟨56435168798099346966590987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623445865399564644393991 56435168798099346966590987)
    ·
      refine ⟨84652753197149020449886481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56435168798099346966590987 84652753197149020449886481)
      ·
        refine ⟨63489564897861765337414861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84652753197149020449886481 63489564897861765337414861)
        ·
          refine ⟨23808586836698162001530573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63489564897861765337414861 23808586836698162001530573)
          ·
            refine ⟨8928220063761810750573965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23808586836698162001530573 8928220063761810750573965)
            ·
              refine ⟨3348082523910679031465237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928220063761810750573965 3348082523910679031465237)
              ·
                refine ⟨156941368308313079599933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3348082523910679031465237 156941368308313079599933)
                ·
                  rfl

theorem cell22_4126170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_4126170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126170 prefixEnd_4126170 := by exact prefixLift 4126170
  have htrace : WordTrace (prefixWord ++ tailWord_4126170) baseStart_4126170 baseEnd_4126170 := by
    simpa [prefixWord, tailWord_4126170, baseEnd_4126170] using wordTrace_append hprefix tailTrace_4126170
  have hstable : (prefixWord ++ tailWord_4126170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126170).length < 2 ^ (prefixWord ++ tailWord_4126170).sum := by decide
  have hdescent : baseEnd_4126170 < baseStart_4126170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126202 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_4126202 : Nat := 118140960795 + 4126202 * 2 ^ 59
def prefixEnd_4126202 : Nat := 4983230072969 + 3 ^ 40 * 4126202 * 2
def baseEnd_4126202 : Nat := 1412483269028780299599299

theorem tailTrace_4126202 : CollatzResearch.WordTrace tailWord_4126202 prefixEnd_4126202 1412483269028780299599299 := by
  unfold tailWord_4126202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623737649370582010685215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100329967064988218695160573 37623737649370582010685215)
  ·
    refine ⟨56435606474055873016027823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623737649370582010685215 56435606474055873016027823)
    ·
      refine ⟨84653409711083809524041735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56435606474055873016027823 84653409711083809524041735)
      ·
        refine ⟨126980114566625714286062603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84653409711083809524041735 126980114566625714286062603)
        ·
          refine ⟨190470171849938571429093905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126980114566625714286062603 190470171849938571429093905)
          ·
            refine ⟨142852628887453928571820429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190470171849938571429093905 142852628887453928571820429)
            ·
              refine ⟨53569735832795223214432661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142852628887453928571820429 53569735832795223214432661)
              ·
                refine ⟨2511081367162276088176531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53569735832795223214432661 2511081367162276088176531)
                ·
                  refine ⟨3766622050743414132264797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511081367162276088176531 3766622050743414132264797)
                  ·
                    refine ⟨1412483269028780299599299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766622050743414132264797 1412483269028780299599299)
                    ·
                      rfl

theorem cell22_4126202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_4126202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126202 prefixEnd_4126202 := by exact prefixLift 4126202
  have htrace : WordTrace (prefixWord ++ tailWord_4126202) baseStart_4126202 baseEnd_4126202 := by
    simpa [prefixWord, tailWord_4126202, baseEnd_4126202] using wordTrace_append hprefix tailTrace_4126202
  have hstable : (prefixWord ++ tailWord_4126202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126202).length < 2 ^ (prefixWord ++ tailWord_4126202).sum := by decide
  have hdescent : baseEnd_4126202 < baseStart_4126202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126221 : List Nat := [1, 7, 1, 1, 2, 2, 2, 6]
def baseStart_4126221 : Nat := 118140960795 + 4126221 * 2 ^ 59
def prefixEnd_4126221 : Nat := 4983230072969 + 3 ^ 40 * 4126221 * 2
def baseEnd_4126221 : Nat := 156943308124118953708249

theorem tailTrace_4126221 : CollatzResearch.WordTrace tailWord_4126221 prefixEnd_4126221 156943308124118953708249 := by
  unfold tailWord_4126221
  simp only [CollatzResearch.WordTrace]
  refine ⟨150495643584413494287682517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100330429056275662858455011 150495643584413494287682517)
  ·
    refine ⟨3527241646509691272367559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 150495643584413494287682517 3527241646509691272367559)
    ·
      refine ⟨5290862469764536908551339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527241646509691272367559 5290862469764536908551339)
      ·
        refine ⟨7936293704646805362827009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290862469764536908551339 7936293704646805362827009)
        ·
          refine ⟨5952220278485104022120257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936293704646805362827009 5952220278485104022120257)
          ·
            refine ⟨4464165208863828016590193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952220278485104022120257 4464165208863828016590193)
            ·
              refine ⟨3348123906647871012442645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464165208863828016590193 3348123906647871012442645)
              ·
                refine ⟨156943308124118953708249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3348123906647871012442645 156943308124118953708249)
                ·
                  rfl

theorem cell22_4126221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 6].length) (baseStart_4126221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126221 prefixEnd_4126221 := by exact prefixLift 4126221
  have htrace : WordTrace (prefixWord ++ tailWord_4126221) baseStart_4126221 baseEnd_4126221 := by
    simpa [prefixWord, tailWord_4126221, baseEnd_4126221] using wordTrace_append hprefix tailTrace_4126221
  have hstable : (prefixWord ++ tailWord_4126221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126221).length < 2 ^ (prefixWord ++ tailWord_4126221).sum := by decide
  have hdescent : baseEnd_4126221 < baseStart_4126221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126279 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 1, 4]
def baseStart_4126279 : Nat := 118140960795 + 4126279 * 2 ^ 59
def prefixEnd_4126279 : Nat := 4983230072969 + 3 ^ 40 * 4126279 * 2
def baseEnd_4126279 : Nat := 1412509627702377765424063

theorem tailTrace_4126279 : CollatzResearch.WordTrace tailWord_4126279 prefixEnd_4126279 1412509627702377765424063 := by
  unfold tailWord_4126279
  simp only [CollatzResearch.WordTrace]
  refine ⟨150497759018203370193293891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100331839345468913462195927 150497759018203370193293891)
  ·
    refine ⟨225746638527305055289940837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150497759018203370193293891 225746638527305055289940837)
    ·
      refine ⟨42327494723869697866863907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225746638527305055289940837 42327494723869697866863907)
      ·
        refine ⟨63491242085804546800295861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42327494723869697866863907 63491242085804546800295861)
        ·
          refine ⟨5952303945544176262527737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63491242085804546800295861 5952303945544176262527737)
          ·
            refine ⟨4464227959158132196895803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952303945544176262527737 4464227959158132196895803)
            ·
              refine ⟨6696341938737198295343705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464227959158132196895803 6696341938737198295343705)
              ·
                refine ⟨5022256454052898721507779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696341938737198295343705 5022256454052898721507779)
                ·
                  refine ⟨7533384681079348082261669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022256454052898721507779 7533384681079348082261669)
                  ·
                    refine ⟨1412509627702377765424063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7533384681079348082261669 1412509627702377765424063)
                    ·
                      rfl

theorem cell22_4126279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_4126279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126279 prefixEnd_4126279 := by exact prefixLift 4126279
  have htrace : WordTrace (prefixWord ++ tailWord_4126279) baseStart_4126279 baseEnd_4126279 := by
    simpa [prefixWord, tailWord_4126279, baseEnd_4126279] using wordTrace_append hprefix tailTrace_4126279
  have hstable : (prefixWord ++ tailWord_4126279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126279).length < 2 ^ (prefixWord ++ tailWord_4126279).sum := by decide
  have hdescent : baseEnd_4126279 < baseStart_4126279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126288 : List Nat := [2, 1, 1, 1, 1, 3, 3, 10]
def baseStart_4126288 : Nat := 118140960795 + 4126288 * 2 ^ 59
def prefixEnd_4126288 : Nat := 4983230072969 + 3 ^ 40 * 4126288 * 2
def baseEnd_4126288 : Nat := 156945856509589415772115

theorem tailTrace_4126288 : CollatzResearch.WordTrace tailWord_4126288 prefixEnd_4126288 156945856509589415772115 := by
  unfold tailWord_4126288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75249043637585382365185759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100332058183447176486914345 75249043637585382365185759)
  ·
    refine ⟨112873565456378073547778639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75249043637585382365185759 112873565456378073547778639)
    ·
      refine ⟨169310348184567110321667959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112873565456378073547778639 169310348184567110321667959)
      ·
        refine ⟨253965522276850665482501939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169310348184567110321667959 253965522276850665482501939)
        ·
          refine ⟨380948283415275998223752909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253965522276850665482501939 380948283415275998223752909)
          ·
            refine ⟨142855606280728499333907341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380948283415275998223752909 142855606280728499333907341)
            ·
              refine ⟨53570852355273187250215253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142855606280728499333907341 53570852355273187250215253)
              ·
                refine ⟨156945856509589415772115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53570852355273187250215253 156945856509589415772115)
                ·
                  rfl

theorem cell22_4126288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_4126288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126288 prefixEnd_4126288 := by exact prefixLift 4126288
  have htrace : WordTrace (prefixWord ++ tailWord_4126288) baseStart_4126288 baseEnd_4126288 := by
    simpa [prefixWord, tailWord_4126288, baseEnd_4126288] using wordTrace_append hprefix tailTrace_4126288
  have hstable : (prefixWord ++ tailWord_4126288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126288).length < 2 ^ (prefixWord ++ tailWord_4126288).sum := by decide
  have hdescent : baseEnd_4126288 < baseStart_4126288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126309 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_4126309 : Nat := 118140960795 + 4126309 * 2 ^ 59
def prefixEnd_4126309 : Nat := 4983230072969 + 3 ^ 40 * 4126309 * 2
def baseEnd_4126309 : Nat := 1412519897315467687173971

theorem tailTrace_4126309 : CollatzResearch.WordTrace tailWord_4126309 prefixEnd_4126309 1412519897315467687173971 := by
  unfold tailWord_4126309
  simp only [CollatzResearch.WordTrace]
  refine ⟨150498853208094685316885981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100332568805396456877923987 150498853208094685316885981)
  ·
    refine ⟨56437069953035506993832243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150498853208094685316885981 56437069953035506993832243)
    ·
      refine ⟨84655604929553260490748365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56437069953035506993832243 84655604929553260490748365)
      ·
        refine ⟨31745851848582472684030637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84655604929553260490748365 31745851848582472684030637)
        ·
          refine ⟨11904694443218427256511489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31745851848582472684030637 11904694443218427256511489)
          ·
            refine ⟨8928520832413820442383617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11904694443218427256511489 8928520832413820442383617)
            ·
              refine ⟨6696390624310365331787713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8928520832413820442383617 6696390624310365331787713)
              ·
                refine ⟨5022292968232773998840785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696390624310365331787713 5022292968232773998840785)
                ·
                  refine ⟨3766719726174580499130589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5022292968232773998840785 3766719726174580499130589)
                  ·
                    refine ⟨1412519897315467687173971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766719726174580499130589 1412519897315467687173971)
                    ·
                      rfl

theorem cell22_4126309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_4126309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126309 prefixEnd_4126309 := by exact prefixLift 4126309
  have htrace : WordTrace (prefixWord ++ tailWord_4126309) baseStart_4126309 baseEnd_4126309 := by
    simpa [prefixWord, tailWord_4126309, baseEnd_4126309] using wordTrace_append hprefix tailTrace_4126309
  have hstable : (prefixWord ++ tailWord_4126309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126309).length < 2 ^ (prefixWord ++ tailWord_4126309).sum := by decide
  have hdescent : baseEnd_4126309 < baseStart_4126309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126322 : List Nat := [3, 2, 1, 2, 3, 3, 1, 7]
def baseStart_4126322 : Nat := 118140960795 + 4126322 * 2 ^ 59
def prefixEnd_4126322 : Nat := 4983230072969 + 3 ^ 40 * 4126322 * 2
def baseEnd_4126322 : Nat := 156947149720126665177659

theorem tailTrace_4126322 : CollatzResearch.WordTrace tailWord_4126322 prefixEnd_4126322 156947149720126665177659 := by
  unfold tailWord_4126322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624831839261897134277305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100332884904698392358072813 37624831839261897134277305)
  ·
    refine ⟨28218623879446422850707979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37624831839261897134277305 28218623879446422850707979)
    ·
      refine ⟨42327935819169634276061969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28218623879446422850707979 42327935819169634276061969)
      ·
        refine ⟨31745951864377225707046477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42327935819169634276061969 31745951864377225707046477)
        ·
          refine ⟨11904731949141459640142429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31745951864377225707046477 11904731949141459640142429)
          ·
            refine ⟨4464274480928047365053411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11904731949141459640142429 4464274480928047365053411)
            ·
              refine ⟨6696411721392071047580117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464274480928047365053411 6696411721392071047580117)
              ·
                refine ⟨156947149720126665177659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6696411721392071047580117 156947149720126665177659)
                ·
                  rfl

theorem cell22_4126322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_4126322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126322 prefixEnd_4126322 := by exact prefixLift 4126322
  have htrace : WordTrace (prefixWord ++ tailWord_4126322) baseStart_4126322 baseEnd_4126322 := by
    simpa [prefixWord, tailWord_4126322, baseEnd_4126322] using wordTrace_append hprefix tailTrace_4126322
  have hstable : (prefixWord ++ tailWord_4126322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126322).length < 2 ^ (prefixWord ++ tailWord_4126322).sum := by decide
  have hdescent : baseEnd_4126322 < baseStart_4126322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126337 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4126337 : Nat := 118140960795 + 4126337 * 2 ^ 59
def prefixEnd_4126337 : Nat := 4983230072969 + 3 ^ 40 * 4126337 * 2
def baseEnd_4126337 : Nat := 1412529482287684947473885

theorem tailTrace_4126337 : CollatzResearch.WordTrace tailWord_4126337 prefixEnd_4126337 1412529482287684947473885 := by
  unfold tailWord_4126337
  simp only [CollatzResearch.WordTrace]
  refine ⟨150499874451993246098905265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100333249634662164065936843 150499874451993246098905265)
  ·
    refine ⟨112874905838994934574178949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150499874451993246098905265 112874905838994934574178949)
    ·
      refine ⟨21164044844811550232658553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112874905838994934574178949 21164044844811550232658553)
      ·
        refine ⟨15873033633608662674493915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164044844811550232658553 15873033633608662674493915)
        ·
          refine ⟨23809550450412994011740873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873033633608662674493915 23809550450412994011740873)
          ·
            refine ⟨17857162837809745508805655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23809550450412994011740873 17857162837809745508805655)
            ·
              refine ⟨26785744256714618263208483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17857162837809745508805655 26785744256714618263208483)
              ·
                refine ⟨40178616385071927394812725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26785744256714618263208483 40178616385071927394812725)
                ·
                  refine ⟨3766745286100493193263693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40178616385071927394812725 3766745286100493193263693)
                  ·
                    refine ⟨1412529482287684947473885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766745286100493193263693 1412529482287684947473885)
                    ·
                      rfl

theorem cell22_4126337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4126337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126337 prefixEnd_4126337 := by exact prefixLift 4126337
  have htrace : WordTrace (prefixWord ++ tailWord_4126337) baseStart_4126337 baseEnd_4126337 := by
    simpa [prefixWord, tailWord_4126337, baseEnd_4126337] using wordTrace_append hprefix tailTrace_4126337
  have hstable : (prefixWord ++ tailWord_4126337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126337).length < 2 ^ (prefixWord ++ tailWord_4126337).sum := by decide
  have hdescent : baseEnd_4126337 < baseStart_4126337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126422 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4126422 : Nat := 118140960795 + 4126422 * 2 ^ 59
def prefixEnd_4126422 : Nat := 4983230072969 + 3 ^ 40 * 4126422 * 2
def baseEnd_4126422 : Nat := 1412558579524773059098625

theorem tailTrace_4126422 : CollatzResearch.WordTrace tailWord_4126422 prefixEnd_4126422 1412558579524773059098625 := by
  unfold tailWord_4126422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406435916042831600984345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100335316437790203743833013 9406435916042831600984345)
  ·
    refine ⟨7054826937032123700738259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9406435916042831600984345 7054826937032123700738259)
    ·
      refine ⟨10582240405548185551107389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054826937032123700738259 10582240405548185551107389)
      ·
        refine ⟨3968340152080569581665271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10582240405548185551107389 3968340152080569581665271)
        ·
          refine ⟨5952510228120854372497907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968340152080569581665271 5952510228120854372497907)
          ·
            refine ⟨8928765342181281558746861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952510228120854372497907 8928765342181281558746861)
            ·
              refine ⟨3348287003317980584530073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928765342181281558746861 3348287003317980584530073)
              ·
                refine ⟨2511215252488485438397555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348287003317980584530073 2511215252488485438397555)
                ·
                  refine ⟨3766822878732728157596333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511215252488485438397555 3766822878732728157596333)
                  ·
                    refine ⟨1412558579524773059098625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3766822878732728157596333 1412558579524773059098625)
                    ·
                      rfl

theorem cell22_4126422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4126422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126422 prefixEnd_4126422 := by exact prefixLift 4126422
  have htrace : WordTrace (prefixWord ++ tailWord_4126422) baseStart_4126422 baseEnd_4126422 := by
    simpa [prefixWord, tailWord_4126422, baseEnd_4126422] using wordTrace_append hprefix tailTrace_4126422
  have hstable : (prefixWord ++ tailWord_4126422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126422).length < 2 ^ (prefixWord ++ tailWord_4126422).sum := by decide
  have hdescent : baseEnd_4126422 < baseStart_4126422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126455 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4126455 : Nat := 118140960795 + 4126455 * 2 ^ 59
def prefixEnd_4126455 : Nat := 4983230072969 + 3 ^ 40 * 4126455 * 2
def baseEnd_4126455 : Nat := 1412569876099171973023523

theorem tailTrace_4126455 : CollatzResearch.WordTrace tailWord_4126455 prefixEnd_4126455 1412569876099171973023523 := by
  unfold tailWord_4126455
  simp only [CollatzResearch.WordTrace]
  refine ⟨150504178265565752251700819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100336118843710501501133879 150504178265565752251700819)
  ·
    refine ⟨225756267398348628377551229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150504178265565752251700819 225756267398348628377551229)
    ·
      refine ⟨84658600274380735641581711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225756267398348628377551229 84658600274380735641581711)
      ·
        refine ⟨126987900411571103462372567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84658600274380735641581711 126987900411571103462372567)
        ·
          refine ⟨190481850617356655193558851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126987900411571103462372567 190481850617356655193558851)
          ·
            refine ⟨285722775926034982790338277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190481850617356655193558851 285722775926034982790338277)
            ·
              refine ⟨53573020486131559273188427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285722775926034982790338277 53573020486131559273188427)
              ·
                refine ⟨80359530729197338909782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53573020486131559273188427 80359530729197338909782641)
                ·
                  refine ⟨60269648046898004182336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80359530729197338909782641 60269648046898004182336981)
                  ·
                    refine ⟨1412569876099171973023523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60269648046898004182336981 1412569876099171973023523)
                    ·
                      rfl

theorem cell22_4126455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4126455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126455 prefixEnd_4126455 := by exact prefixLift 4126455
  have htrace : WordTrace (prefixWord ++ tailWord_4126455) baseStart_4126455 baseEnd_4126455 := by
    simpa [prefixWord, tailWord_4126455, baseEnd_4126455] using wordTrace_append hprefix tailTrace_4126455
  have hstable : (prefixWord ++ tailWord_4126455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126455).length < 2 ^ (prefixWord ++ tailWord_4126455).sum := by decide
  have hdescent : baseEnd_4126455 < baseStart_4126455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126487 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_4126487 : Nat := 118140960795 + 4126487 * 2 ^ 59
def prefixEnd_4126487 : Nat := 4983230072969 + 3 ^ 40 * 4126487 * 2
def baseEnd_4126487 : Nat := 1412580830353134556223425

theorem tailTrace_4126487 : CollatzResearch.WordTrace tailWord_4126487 prefixEnd_4126487 1412580830353134556223425 := by
  unfold tailWord_4126487
  simp only [CollatzResearch.WordTrace]
  refine ⟨150505345401449821716865715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100336896934299881144577143 150505345401449821716865715)
  ·
    refine ⟨225758018102174732575298573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150505345401449821716865715 225758018102174732575298573)
    ·
      refine ⟨84659256788315524715736965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225758018102174732575298573 84659256788315524715736965)
      ·
        refine ⟨15873610647809160884200681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84659256788315524715736965 15873610647809160884200681)
        ·
          refine ⟨11905207985856870663150511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15873610647809160884200681 11905207985856870663150511)
          ·
            refine ⟨17857811978785305994725767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905207985856870663150511 17857811978785305994725767)
            ·
              refine ⟨26786717968177958992088651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17857811978785305994725767 26786717968177958992088651)
              ·
                refine ⟨40180076952266938488132977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26786717968177958992088651 40180076952266938488132977)
                ·
                  refine ⟨30135057714200203866099733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40180076952266938488132977 30135057714200203866099733)
                  ·
                    refine ⟨1412580830353134556223425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30135057714200203866099733 1412580830353134556223425)
                    ·
                      rfl

theorem cell22_4126487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_4126487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126487 prefixEnd_4126487 := by exact prefixLift 4126487
  have htrace : WordTrace (prefixWord ++ tailWord_4126487) baseStart_4126487 baseEnd_4126487 := by
    simpa [prefixWord, tailWord_4126487, baseEnd_4126487] using wordTrace_append hprefix tailTrace_4126487
  have hstable : (prefixWord ++ tailWord_4126487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126487).length < 2 ^ (prefixWord ++ tailWord_4126487).sum := by decide
  have hdescent : baseEnd_4126487 < baseStart_4126487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126577 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4126577 : Nat := 118140960795 + 4126577 * 2 ^ 59
def prefixEnd_4126577 : Nat := 4983230072969 + 3 ^ 40 * 4126577 * 2
def baseEnd_4126577 : Nat := 1412611639192404321473149

theorem tailTrace_4126577 : CollatzResearch.WordTrace tailWord_4126577 prefixEnd_4126577 1412611639192404321473149 := by
  unfold tailWord_4126577
  simp only [CollatzResearch.WordTrace]
  refine ⟨150508627971123767087641985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100339085314082511391761323 150508627971123767087641985)
  ·
    refine ⟨112881470978342825315731489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150508627971123767087641985 112881470978342825315731489)
    ·
      refine ⟨84661103233757118986798617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112881470978342825315731489 84661103233757118986798617)
      ·
        refine ⟨63495827425317839240098963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84661103233757118986798617 63495827425317839240098963)
        ·
          refine ⟨95243741137976758860148445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63495827425317839240098963 95243741137976758860148445)
          ·
            refine ⟨35716402926741284572555667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95243741137976758860148445 35716402926741284572555667)
            ·
              refine ⟨53574604390111926858833501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35716402926741284572555667 53574604390111926858833501)
              ·
                refine ⟨20090476646291972572062563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53574604390111926858833501 20090476646291972572062563)
                ·
                  refine ⟨30135714969437958858093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20090476646291972572062563 30135714969437958858093845)
                  ·
                    refine ⟨1412611639192404321473149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30135714969437958858093845 1412611639192404321473149)
                    ·
                      rfl

theorem cell22_4126577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4126577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126577 prefixEnd_4126577 := by exact prefixLift 4126577
  have htrace : WordTrace (prefixWord ++ tailWord_4126577) baseStart_4126577 baseEnd_4126577 := by
    simpa [prefixWord, tailWord_4126577, baseEnd_4126577] using wordTrace_append hprefix tailTrace_4126577
  have hstable : (prefixWord ++ tailWord_4126577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126577).length < 2 ^ (prefixWord ++ tailWord_4126577).sum := by decide
  have hdescent : baseEnd_4126577 < baseStart_4126577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126624 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_4126624 : Nat := 118140960795 + 4126624 * 2 ^ 59
def prefixEnd_4126624 : Nat := 4983230072969 + 3 ^ 40 * 4126624 * 2
def baseEnd_4126624 : Nat := 1412627728252911865548005

theorem tailTrace_4126624 : CollatzResearch.WordTrace tailWord_4126624 prefixEnd_4126624 1412627728252911865548005 := by
  unfold tailWord_4126624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75255171100976747057301463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100340228134635662743068617 75255171100976747057301463)
  ·
    refine ⟨112882756651465120585952195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75255171100976747057301463 112882756651465120585952195)
    ·
      refine ⟨169324134977197680878928293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112882756651465120585952195 169324134977197680878928293)
      ·
        refine ⟨31748275308224565164799055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169324134977197680878928293 31748275308224565164799055)
        ·
          refine ⟨47622412962336847747198583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31748275308224565164799055 47622412962336847747198583)
          ·
            refine ⟨71433619443505271620797875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47622412962336847747198583 71433619443505271620797875)
            ·
              refine ⟨107150429165257907431196813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71433619443505271620797875 107150429165257907431196813)
              ·
                refine ⟨40181410936971715286698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107150429165257907431196813 40181410936971715286698805)
                ·
                  refine ⟨3767007275341098308128013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40181410936971715286698805 3767007275341098308128013)
                  ·
                    refine ⟨1412627728252911865548005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767007275341098308128013 1412627728252911865548005)
                    ·
                      rfl

theorem cell22_4126624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_4126624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126624 prefixEnd_4126624 := by exact prefixLift 4126624
  have htrace : WordTrace (prefixWord ++ tailWord_4126624) baseStart_4126624 baseEnd_4126624 := by
    simpa [prefixWord, tailWord_4126624, baseEnd_4126624] using wordTrace_append hprefix tailTrace_4126624
  have hstable : (prefixWord ++ tailWord_4126624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126624).length < 2 ^ (prefixWord ++ tailWord_4126624).sum := by decide
  have hdescent : baseEnd_4126624 < baseStart_4126624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126716 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_4126716 : Nat := 118140960795 + 4126716 * 2 ^ 59
def prefixEnd_4126716 : Nat := 4983230072969 + 3 ^ 40 * 4126716 * 2
def baseEnd_4126716 : Nat := 470886407244351430749241

theorem tailTrace_4126716 : CollatzResearch.WordTrace tailWord_4126716 prefixEnd_4126716 470886407244351430749241 := by
  unfold tailWord_4126716
  simp only [CollatzResearch.WordTrace]
  refine ⟨75256848858810096913476001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100342465145080129217968001 75256848858810096913476001)
  ·
    refine ⟨56442636644107572685107001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75256848858810096913476001 56442636644107572685107001)
    ·
      refine ⟨42331977483080679513830251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56442636644107572685107001 42331977483080679513830251)
      ·
        refine ⟨63497966224621019270745377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42331977483080679513830251 63497966224621019270745377)
        ·
          refine ⟨47623474668465764453059033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63497966224621019270745377 47623474668465764453059033)
          ·
            refine ⟨35717606001349323339794275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47623474668465764453059033 35717606001349323339794275)
            ·
              refine ⟨53576409002023985009691413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35717606001349323339794275 53576409002023985009691413)
              ·
                refine ⟨2511394171969874297329285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53576409002023985009691413 2511394171969874297329285)
                ·
                  refine ⟨470886407244351430749241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511394171969874297329285 470886407244351430749241)
                  ·
                    rfl

theorem cell22_4126716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_4126716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126716 prefixEnd_4126716 := by exact prefixLift 4126716
  have htrace : WordTrace (prefixWord ++ tailWord_4126716) baseStart_4126716 baseEnd_4126716 := by
    simpa [prefixWord, tailWord_4126716, baseEnd_4126716] using wordTrace_append hprefix tailTrace_4126716
  have hstable : (prefixWord ++ tailWord_4126716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126716).length < 2 ^ (prefixWord ++ tailWord_4126716).sum := by decide
  have hdescent : baseEnd_4126716 < baseStart_4126716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126744 : List Nat := [2, 1, 2, 3, 2, 1, 3, 8]
def baseStart_4126744 : Nat := 118140960795 + 4126744 * 2 ^ 59
def prefixEnd_4126744 : Nat := 4983230072969 + 3 ^ 40 * 4126744 * 2
def baseEnd_4126744 : Nat := 156963200745030172505293

theorem tailTrace_4126744 : CollatzResearch.WordTrace tailWord_4126744 prefixEnd_4126744 156963200745030172505293 := by
  unfold tailWord_4126744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75257359480759377304485643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100343145974345836405980857 75257359480759377304485643)
  ·
    refine ⟨112886039221139065956728465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75257359480759377304485643 112886039221139065956728465)
    ·
      refine ⟨84664529415854299467546349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112886039221139065956728465 84664529415854299467546349)
      ·
        refine ⟨31749198530945362300329881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84664529415854299467546349 31749198530945362300329881)
        ·
          refine ⟨23811898898209021725247411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31749198530945362300329881 23811898898209021725247411)
          ·
            refine ⟨35717848347313532587871117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23811898898209021725247411 35717848347313532587871117)
            ·
              refine ⟨13394193130242574720451669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35717848347313532587871117 13394193130242574720451669)
              ·
                refine ⟨156963200745030172505293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13394193130242574720451669 156963200745030172505293)
                ·
                  rfl

theorem cell22_4126744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_4126744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126744 prefixEnd_4126744 := by exact prefixLift 4126744
  have htrace : WordTrace (prefixWord ++ tailWord_4126744) baseStart_4126744 baseEnd_4126744 := by
    simpa [prefixWord, tailWord_4126744, baseEnd_4126744] using wordTrace_append hprefix tailTrace_4126744
  have hstable : (prefixWord ++ tailWord_4126744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126744).length < 2 ^ (prefixWord ++ tailWord_4126744).sum := by decide
  have hdescent : baseEnd_4126744 < baseStart_4126744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126838 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4126838 : Nat := 118140960795 + 4126838 * 2 ^ 59
def prefixEnd_4126838 : Nat := 4983230072969 + 3 ^ 40 * 4126838 * 2
def baseEnd_4126838 : Nat := 1412700984826286640697349

theorem tailTrace_4126838 : CollatzResearch.WordTrace tailWord_4126838 prefixEnd_4126838 1412700984826286640697349 := by
  unfold tailWord_4126838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407384213948638041430823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100345431615452139108595445 9407384213948638041430823)
  ·
    refine ⟨14111076320922957062146235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407384213948638041430823 14111076320922957062146235)
    ·
      refine ⟨21166614481384435593219353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111076320922957062146235 21166614481384435593219353)
      ·
        refine ⟨15874960861038326694914515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21166614481384435593219353 15874960861038326694914515)
        ·
          refine ⟨23812441291557490042371773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874960861038326694914515 23812441291557490042371773)
          ·
            refine ⟨8929665484334058765889415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23812441291557490042371773 8929665484334058765889415)
            ·
              refine ⟨13394498226501088148834123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929665484334058765889415 13394498226501088148834123)
              ·
                refine ⟨20091747339751632223251185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394498226501088148834123 20091747339751632223251185)
                ·
                  refine ⟨15068810504813724167438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20091747339751632223251185 15068810504813724167438389)
                  ·
                    refine ⟨1412700984826286640697349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15068810504813724167438389 1412700984826286640697349)
                    ·
                      rfl

theorem cell22_4126838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4126838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126838 prefixEnd_4126838 := by exact prefixLift 4126838
  have htrace : WordTrace (prefixWord ++ tailWord_4126838) baseStart_4126838 baseEnd_4126838 := by
    simpa [prefixWord, tailWord_4126838, baseEnd_4126838] using wordTrace_append hprefix tailTrace_4126838
  have hstable : (prefixWord ++ tailWord_4126838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126838).length < 2 ^ (prefixWord ++ tailWord_4126838).sum := by decide
  have hdescent : baseEnd_4126838 < baseStart_4126838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126851 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 6]
def baseStart_4126851 : Nat := 118140960795 + 4126851 * 2 ^ 59
def prefixEnd_4126851 : Nat := 4983230072969 + 3 ^ 40 * 4126851 * 2
def baseEnd_4126851 : Nat := 470901811663986313374103

theorem tailTrace_4126851 : CollatzResearch.WordTrace tailWord_4126851 prefixEnd_4126851 470901811663986313374103 := by
  unfold tailWord_4126851
  simp only [CollatzResearch.WordTrace]
  refine ⟨150518621572131111883116407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100345747714754074588744271 150518621572131111883116407)
  ·
    refine ⟨225777932358196667824674611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150518621572131111883116407 225777932358196667824674611)
    ·
      refine ⟨338666898537295001737011917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225777932358196667824674611 338666898537295001737011917)
      ·
        refine ⟨127000086951485625651379469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338666898537295001737011917 127000086951485625651379469)
        ·
          refine ⟨47625032606807109619267301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127000086951485625651379469 47625032606807109619267301)
          ·
            refine ⟨8929693613776333053612619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47625032606807109619267301 8929693613776333053612619)
            ·
              refine ⟨13394540420664499580418929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929693613776333053612619 13394540420664499580418929)
              ·
                refine ⟨10045905315498374685314197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13394540420664499580418929 10045905315498374685314197)
                ·
                  refine ⟨470901811663986313374103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10045905315498374685314197 470901811663986313374103)
                  ·
                    rfl

theorem cell22_4126851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_4126851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126851 prefixEnd_4126851 := by exact prefixLift 4126851
  have htrace : WordTrace (prefixWord ++ tailWord_4126851) baseStart_4126851 baseEnd_4126851 := by
    simpa [prefixWord, tailWord_4126851, baseEnd_4126851] using wordTrace_append hprefix tailTrace_4126851
  have hstable : (prefixWord ++ tailWord_4126851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126851).length < 2 ^ (prefixWord ++ tailWord_4126851).sum := by decide
  have hdescent : baseEnd_4126851 < baseStart_4126851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126956 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_4126956 : Nat := 118140960795 + 4126956 * 2 ^ 59
def prefixEnd_4126956 : Nat := 4983230072969 + 3 ^ 40 * 4126956 * 2
def baseEnd_4126956 : Nat := 1412741378637773666246987

theorem tailTrace_4126956 : CollatzResearch.WordTrace tailWord_4126956 prefixEnd_4126956 1412741378637773666246987 := by
  unfold tailWord_4126956
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261225618375357407844361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100348300824500476543792481 75261225618375357407844361)
  ·
    refine ⟨56445919213781518055883271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75261225618375357407844361 56445919213781518055883271)
    ·
      refine ⟨84668878820672277083824907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56445919213781518055883271 84668878820672277083824907)
      ·
        refine ⟨127003318231008415625737361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84668878820672277083824907 127003318231008415625737361)
        ·
          refine ⟨95252488673256311719303021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127003318231008415625737361 95252488673256311719303021)
          ·
            refine ⟨35719683252471116894738633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95252488673256311719303021 35719683252471116894738633)
            ·
              refine ⟨26789762439353337671053975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35719683252471116894738633 26789762439353337671053975)
              ·
                refine ⟨40184643659030006506580963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26789762439353337671053975 40184643659030006506580963)
                ·
                  refine ⟨60276965488545009759871445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40184643659030006506580963 60276965488545009759871445)
                  ·
                    refine ⟨1412741378637773666246987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60276965488545009759871445 1412741378637773666246987)
                    ·
                      rfl

theorem cell22_4126956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_4126956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4126956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4126956 prefixEnd_4126956 := by exact prefixLift 4126956
  have htrace : WordTrace (prefixWord ++ tailWord_4126956) baseStart_4126956 baseEnd_4126956 := by
    simpa [prefixWord, tailWord_4126956, baseEnd_4126956] using wordTrace_append hprefix tailTrace_4126956
  have hstable : (prefixWord ++ tailWord_4126956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126956).length < 2 ^ (prefixWord ++ tailWord_4126956).sum := by decide
  have hdescent : baseEnd_4126956 < baseStart_4126956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127031 : List Nat := [1, 1, 3, 1, 2, 1, 1, 12]
def baseStart_4127031 : Nat := 118140960795 + 4127031 * 2 ^ 59
def prefixEnd_4127031 : Nat := 4983230072969 + 3 ^ 40 * 4127031 * 2
def baseEnd_4127031 : Nat := 156974116963388718957973

theorem tailTrace_4127031 : CollatzResearch.WordTrace tailWord_4127031 prefixEnd_4127031 156974116963388718957973 := by
  unfold tailWord_4127031
  simp only [CollatzResearch.WordTrace]
  refine ⟨150525186711479002624668947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100350124474319335083112631 150525186711479002624668947)
  ·
    refine ⟨225787780067218503937003421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150525186711479002624668947 225787780067218503937003421)
    ·
      refine ⟨84670417525206938976376283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225787780067218503937003421 84670417525206938976376283)
      ·
        refine ⟨127005626287810408464564425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84670417525206938976376283 127005626287810408464564425)
        ·
          refine ⟨95254219715857806348423319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127005626287810408464564425 95254219715857806348423319)
          ·
            refine ⟨142881329573786709522634979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95254219715857806348423319 142881329573786709522634979)
            ·
              refine ⟨214321994360680064283952469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142881329573786709522634979 214321994360680064283952469)
              ·
                refine ⟨156974116963388718957973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 214321994360680064283952469 156974116963388718957973)
                ·
                  rfl

theorem cell22_4127031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 12].length) (baseStart_4127031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127031 prefixEnd_4127031 := by exact prefixLift 4127031
  have htrace : WordTrace (prefixWord ++ tailWord_4127031) baseStart_4127031 baseEnd_4127031 := by
    simpa [prefixWord, tailWord_4127031, baseEnd_4127031] using wordTrace_append hprefix tailTrace_4127031
  have hstable : (prefixWord ++ tailWord_4127031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127031).length < 2 ^ (prefixWord ++ tailWord_4127031).sum := by decide
  have hdescent : baseEnd_4127031 < baseStart_4127031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127082 : List Nat := [3, 1, 3, 3, 1, 3, 2, 6]
def baseStart_4127082 : Nat := 118140960795 + 4127082 * 2 ^ 59
def prefixEnd_4127082 : Nat := 4983230072969 + 3 ^ 40 * 4127082 * 2
def baseEnd_4127082 : Nat := 156976056779194593066289

theorem tailTrace_4127082 : CollatzResearch.WordTrace tailWord_4127082 prefixEnd_4127082 156976056779194593066289 := by
  unfold tailWord_4127082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37631761708573559583693875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100351364556196158889850333 37631761708573559583693875)
  ·
    refine ⟨56447642562860339375540813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37631761708573559583693875 56447642562860339375540813)
    ·
      refine ⟨21167865961072627265827805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56447642562860339375540813 21167865961072627265827805)
      ·
        refine ⟨7937949735402235224685427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21167865961072627265827805 7937949735402235224685427)
        ·
          refine ⟨11906924603103352837028141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937949735402235224685427 11906924603103352837028141)
          ·
            refine ⟨4465096726163757313885553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11906924603103352837028141 4465096726163757313885553)
            ·
              refine ⟨3348822544622817985414165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465096726163757313885553 3348822544622817985414165)
              ·
                refine ⟨156976056779194593066289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3348822544622817985414165 156976056779194593066289)
                ·
                  rfl

theorem cell22_4127082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_4127082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127082 prefixEnd_4127082 := by exact prefixLift 4127082
  have htrace : WordTrace (prefixWord ++ tailWord_4127082) baseStart_4127082 baseEnd_4127082 := by
    simpa [prefixWord, tailWord_4127082, baseEnd_4127082] using wordTrace_append hprefix tailTrace_4127082
  have hstable : (prefixWord ++ tailWord_4127082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127082).length < 2 ^ (prefixWord ++ tailWord_4127082).sum := by decide
  have hdescent : baseEnd_4127082 < baseStart_4127082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127168 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_4127168 : Nat := 118140960795 + 4127168 * 2 ^ 59
def prefixEnd_4127168 : Nat := 4983230072969 + 3 ^ 40 * 4127168 * 2
def baseEnd_4127168 : Nat := 1412813950570275779946337

theorem tailTrace_4127168 : CollatzResearch.WordTrace tailWord_4127168 prefixEnd_4127168 1412813950570275779946337 := by
  unfold tailWord_4127168
  simp only [CollatzResearch.WordTrace]
  refine ⟨75265091755991337511203079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100353455674655116681604105 75265091755991337511203079)
  ·
    refine ⟨112897637633987006266804619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75265091755991337511203079 112897637633987006266804619)
    ·
      refine ⟨169346456450980509400206929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112897637633987006266804619 169346456450980509400206929)
      ·
        refine ⟨127009842338235382050155197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169346456450980509400206929 127009842338235382050155197)
        ·
          refine ⟨47628690876838268268808199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127009842338235382050155197 47628690876838268268808199)
          ·
            refine ⟨71443036315257402403212299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47628690876838268268808199 71443036315257402403212299)
            ·
              refine ⟨107164554472886103604818449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71443036315257402403212299 107164554472886103604818449)
              ·
                refine ⟨80373415854664577703613837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107164554472886103604818449 80373415854664577703613837)
                ·
                  refine ⟨30140030945499216638855189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80373415854664577703613837 30140030945499216638855189)
                  ·
                    refine ⟨1412813950570275779946337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30140030945499216638855189 1412813950570275779946337)
                    ·
                      rfl

theorem cell22_4127168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_4127168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127168 prefixEnd_4127168 := by exact prefixLift 4127168
  have htrace : WordTrace (prefixWord ++ tailWord_4127168) baseStart_4127168 baseEnd_4127168 := by
    simpa [prefixWord, tailWord_4127168, baseEnd_4127168] using wordTrace_append hprefix tailTrace_4127168
  have hstable : (prefixWord ++ tailWord_4127168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127168).length < 2 ^ (prefixWord ++ tailWord_4127168).sum := by decide
  have hdescent : baseEnd_4127168 < baseStart_4127168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127200 : List Nat := [2, 1, 1, 3, 1, 1, 7, 6]
def baseStart_4127200 : Nat := 118140960795 + 4127200 * 2 ^ 59
def prefixEnd_4127200 : Nat := 4983230072969 + 3 ^ 40 * 4127200 * 2
def baseEnd_4127200 : Nat := 156980544980470929238471

theorem tailTrace_4127200 : CollatzResearch.WordTrace tailWord_4127200 prefixEnd_4127200 156980544980470929238471 := by
  unfold tailWord_4127200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75265675323933372243785527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100354233765244496325047369 75265675323933372243785527)
  ·
    refine ⟨112898512985900058365678291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75265675323933372243785527 112898512985900058365678291)
    ·
      refine ⟨169347769478850087548517437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112898512985900058365678291 169347769478850087548517437)
      ·
        refine ⟨63505413554568782830694039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169347769478850087548517437 63505413554568782830694039)
        ·
          refine ⟨95258120331853174246041059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63505413554568782830694039 95258120331853174246041059)
          ·
            refine ⟨142887180497779761369061589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95258120331853174246041059 142887180497779761369061589)
            ·
              refine ⟨3348918292916713157087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142887180497779761369061589 3348918292916713157087381)
              ·
                refine ⟨156980544980470929238471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3348918292916713157087381 156980544980470929238471)
                ·
                  rfl

theorem cell22_4127200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_4127200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127200 prefixEnd_4127200 := by exact prefixLift 4127200
  have htrace : WordTrace (prefixWord ++ tailWord_4127200) baseStart_4127200 baseEnd_4127200 := by
    simpa [prefixWord, tailWord_4127200, baseEnd_4127200] using wordTrace_append hprefix tailTrace_4127200
  have hstable : (prefixWord ++ tailWord_4127200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127200).length < 2 ^ (prefixWord ++ tailWord_4127200).sum := by decide
  have hdescent : baseEnd_4127200 < baseStart_4127200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127215 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 7, 3]
def baseStart_4127215 : Nat := 118140960795 + 4127215 * 2 ^ 59
def prefixEnd_4127215 : Nat := 4983230072969 + 3 ^ 40 * 4127215 * 2
def baseEnd_4127215 : Nat := 1412830039630783324021193

theorem tailTrace_4127215 : CollatzResearch.WordTrace tailWord_4127215 prefixEnd_4127215 1412830039630783324021193 := by
  unfold tailWord_4127215
  simp only [CollatzResearch.WordTrace]
  refine ⟨150531897742812402049367099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100354598495208268032911399 150531897742812402049367099)
  ·
    refine ⟨225797846614218603074050649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150531897742812402049367099 225797846614218603074050649)
    ·
      refine ⟨169348384960663952305537987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225797846614218603074050649 169348384960663952305537987)
      ·
        refine ⟨254022577440995928458306981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169348384960663952305537987 254022577440995928458306981)
        ·
          refine ⟨47629233270186736585932559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254022577440995928458306981 47629233270186736585932559)
          ·
            refine ⟨71443849905280104878898839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47629233270186736585932559 71443849905280104878898839)
            ·
              refine ⟨107165774857920157318348259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71443849905280104878898839 107165774857920157318348259)
              ·
                refine ⟨160748662286880235977522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107165774857920157318348259 160748662286880235977522389)
                ·
                  refine ⟨3767546772348755530723181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160748662286880235977522389 3767546772348755530723181)
                  ·
                    refine ⟨1412830039630783324021193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767546772348755530723181 1412830039630783324021193)
                    ·
                      rfl

theorem cell22_4127215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_4127215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127215 prefixEnd_4127215 := by exact prefixLift 4127215
  have htrace : WordTrace (prefixWord ++ tailWord_4127215) baseStart_4127215 baseEnd_4127215 := by
    simpa [prefixWord, tailWord_4127215, baseEnd_4127215] using wordTrace_append hprefix tailTrace_4127215
  have hstable : (prefixWord ++ tailWord_4127215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127215).length < 2 ^ (prefixWord ++ tailWord_4127215).sum := by decide
  have hdescent : baseEnd_4127215 < baseStart_4127215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127238 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4127238 : Nat := 118140960795 + 4127238 * 2 ^ 59
def prefixEnd_4127238 : Nat := 4983230072969 + 3 ^ 40 * 4127238 * 2
def baseEnd_4127238 : Nat := 1412837913000818930696123

theorem tailTrace_4127238 : CollatzResearch.WordTrace tailWord_4127238 prefixEnd_4127238 1412837913000818930696123 := by
  unfold tailWord_4127238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704148019429033655545449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100355157747819384651636245 4704148019429033655545449)
  ·
    refine ⟨3528111014571775241659087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4704148019429033655545449 3528111014571775241659087)
    ·
      refine ⟨5292166521857662862488631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528111014571775241659087 5292166521857662862488631)
      ·
        refine ⟨7938249782786494293732947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292166521857662862488631 7938249782786494293732947)
        ·
          refine ⟨11907374674179741440599421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938249782786494293732947 11907374674179741440599421)
          ·
            refine ⟨4465265502817403040224783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11907374674179741440599421 4465265502817403040224783)
            ·
              refine ⟨6697898254226104560337175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465265502817403040224783 6697898254226104560337175)
              ·
                refine ⟨10046847381339156840505763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697898254226104560337175 10046847381339156840505763)
                ·
                  refine ⟨15070271072008735260758645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046847381339156840505763 15070271072008735260758645)
                  ·
                    refine ⟨1412837913000818930696123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15070271072008735260758645 1412837913000818930696123)
                    ·
                      rfl

theorem cell22_4127238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4127238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127238 prefixEnd_4127238 := by exact prefixLift 4127238
  have htrace : WordTrace (prefixWord ++ tailWord_4127238) baseStart_4127238 baseEnd_4127238 := by
    simpa [prefixWord, tailWord_4127238, baseEnd_4127238] using wordTrace_append hprefix tailTrace_4127238
  have hstable : (prefixWord ++ tailWord_4127238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127238).length < 2 ^ (prefixWord ++ tailWord_4127238).sum := by decide
  have hdescent : baseEnd_4127238 < baseStart_4127238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127309 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4127309 : Nat := 118140960795 + 4127309 * 2 ^ 59
def prefixEnd_4127309 : Nat := 4983230072969 + 3 ^ 40 * 4127309 * 2
def baseEnd_4127309 : Nat := 1412862217751798412170905

theorem tailTrace_4127309 : CollatzResearch.WordTrace tailWord_4127309 prefixEnd_4127309 1412862217751798412170905 := by
  unfold tailWord_4127309
  simp only [CollatzResearch.WordTrace]
  refine ⟨150535326204471856103288981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100356884136314570735525987 150535326204471856103288981)
  ·
    refine ⟨7056343415834618254841671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150535326204471856103288981 7056343415834618254841671)
    ·
      refine ⟨10584515123751927382262507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056343415834618254841671 10584515123751927382262507)
      ·
        refine ⟨15876772685627891073393761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584515123751927382262507 15876772685627891073393761)
        ·
          refine ⟨11907579514220918305045321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15876772685627891073393761 11907579514220918305045321)
          ·
            refine ⟨8930684635665688728783991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11907579514220918305045321 8930684635665688728783991)
            ·
              refine ⟨13396026953498533093175987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930684635665688728783991 13396026953498533093175987)
              ·
                refine ⟨20094040430247799639763981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13396026953498533093175987 20094040430247799639763981)
                ·
                  refine ⟨7535265161342924864911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20094040430247799639763981 7535265161342924864911493)
                  ·
                    refine ⟨1412862217751798412170905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535265161342924864911493 1412862217751798412170905)
                    ·
                      rfl

theorem cell22_4127309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4127309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127309 prefixEnd_4127309 := by exact prefixLift 4127309
  have htrace : WordTrace (prefixWord ++ tailWord_4127309) baseStart_4127309 baseEnd_4127309 := by
    simpa [prefixWord, tailWord_4127309, baseEnd_4127309] using wordTrace_append hprefix tailTrace_4127309
  have hstable : (prefixWord ++ tailWord_4127309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127309).length < 2 ^ (prefixWord ++ tailWord_4127309).sum := by decide
  have hdescent : baseEnd_4127309 < baseStart_4127309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127320 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_4127320 : Nat := 118140960795 + 4127320 * 2 ^ 59
def prefixEnd_4127320 : Nat := 4983230072969 + 3 ^ 40 * 4127320 * 2
def baseEnd_4127320 : Nat := 1412865983276598050145871

theorem tailTrace_4127320 : CollatzResearch.WordTrace tailWord_4127320 prefixEnd_4127320 1412865983276598050145871 := by
  unfold tailWord_4127320
  simp only [CollatzResearch.WordTrace]
  refine ⟨75267863703716002490969707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100357151604954669987959609 75267863703716002490969707)
  ·
    refine ⟨112901795555574003736454561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75267863703716002490969707 112901795555574003736454561)
    ·
      refine ⟨84676346666680502802340921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112901795555574003736454561 84676346666680502802340921)
      ·
        refine ⟨63507260000010377101755691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84676346666680502802340921 63507260000010377101755691)
        ·
          refine ⟨95260890000015565652633537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63507260000010377101755691 95260890000015565652633537)
          ·
            refine ⟨71445667500011674239475153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95260890000015565652633537 71445667500011674239475153)
            ·
              refine ⟨53584250625008755679606365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71445667500011674239475153 53584250625008755679606365)
              ·
                refine ⟨20094093984378283379852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53584250625008755679606365 20094093984378283379852387)
                ·
                  refine ⟨30141140976567425069778581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20094093984378283379852387 30141140976567425069778581)
                  ·
                    refine ⟨1412865983276598050145871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30141140976567425069778581 1412865983276598050145871)
                    ·
                      rfl

theorem cell22_4127320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_4127320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127320 prefixEnd_4127320 := by exact prefixLift 4127320
  have htrace : WordTrace (prefixWord ++ tailWord_4127320) baseStart_4127320 baseEnd_4127320 := by
    simpa [prefixWord, tailWord_4127320, baseEnd_4127320] using wordTrace_append hprefix tailTrace_4127320
  have hstable : (prefixWord ++ tailWord_4127320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127320).length < 2 ^ (prefixWord ++ tailWord_4127320).sum := by decide
  have hdescent : baseEnd_4127320 < baseStart_4127320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127341 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 4]
def baseStart_4127341 : Nat := 118140960795 + 4127341 * 2 ^ 59
def prefixEnd_4127341 : Nat := 4983230072969 + 3 ^ 40 * 4127341 * 2
def baseEnd_4127341 : Nat := 470957724001920331790269

theorem tailTrace_4127341 : CollatzResearch.WordTrace tailWord_4127341 prefixEnd_4127341 470957724001920331790269 := by
  unfold tailWord_4127341
  simp only [CollatzResearch.WordTrace]
  refine ⟨150536493340355925568453877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100357662226903950378969251 150536493340355925568453877)
  ·
    refine ⟨14112796250658368022042551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150536493340355925568453877 14112796250658368022042551)
    ·
      refine ⟨21169194375987552033063827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14112796250658368022042551 21169194375987552033063827)
      ·
        refine ⟨31753791563981328049595741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21169194375987552033063827 31753791563981328049595741)
        ·
          refine ⟨11907671836492998018598403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31753791563981328049595741 11907671836492998018598403)
          ·
            refine ⟨17861507754739497027897605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11907671836492998018598403 17861507754739497027897605)
            ·
              refine ⟨3349032704013655692730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17861507754739497027897605 3349032704013655692730801)
              ·
                refine ⟨2511774528010241769548101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349032704013655692730801 2511774528010241769548101)
                ·
                  refine ⟨470957724001920331790269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511774528010241769548101 470957724001920331790269)
                  ·
                    rfl

theorem cell22_4127341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_4127341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127341 prefixEnd_4127341 := by exact prefixLift 4127341
  have htrace : WordTrace (prefixWord ++ tailWord_4127341) baseStart_4127341 baseEnd_4127341 := by
    simpa [prefixWord, tailWord_4127341, baseEnd_4127341] using wordTrace_append hprefix tailTrace_4127341
  have hstable : (prefixWord ++ tailWord_4127341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127341).length < 2 ^ (prefixWord ++ tailWord_4127341).sum := by decide
  have hdescent : baseEnd_4127341 < baseStart_4127341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127459 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 6]
def baseStart_4127459 : Nat := 118140960795 + 4127459 * 2 ^ 59
def prefixEnd_4127459 : Nat := 4983230072969 + 3 ^ 40 * 4127459 * 2
def baseEnd_4127459 : Nat := 470971188605749340306815

theorem tailTrace_4127459 : CollatzResearch.WordTrace tailWord_4127459 prefixEnd_4127459 470971188605749340306815 := by
  unfold tailWord_4127459
  simp only [CollatzResearch.WordTrace]
  refine ⟨150540797153928431721249431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100360531435952287814166287 150540797153928431721249431)
  ·
    refine ⟨225811195730892647581874147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150540797153928431721249431 225811195730892647581874147)
    ·
      refine ⟨338716793596338971372811221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225811195730892647581874147 338716793596338971372811221)
      ·
        refine ⟨7938674849914194641550263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 338716793596338971372811221 7938674849914194641550263)
        ·
          refine ⟨11908012274871291962325395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938674849914194641550263 11908012274871291962325395)
          ·
            refine ⟨17862018412306937943488093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908012274871291962325395 17862018412306937943488093)
            ·
              refine ⟨6698256904615101728808035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17862018412306937943488093 6698256904615101728808035)
              ·
                refine ⟨10047385356922652593212053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698256904615101728808035 10047385356922652593212053)
                ·
                  refine ⟨470971188605749340306815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10047385356922652593212053 470971188605749340306815)
                  ·
                    rfl

theorem cell22_4127459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_4127459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127459 prefixEnd_4127459 := by exact prefixLift 4127459
  have htrace : WordTrace (prefixWord ++ tailWord_4127459) baseStart_4127459 baseEnd_4127459 := by
    simpa [prefixWord, tailWord_4127459, baseEnd_4127459] using wordTrace_append hprefix tailTrace_4127459
  have hstable : (prefixWord ++ tailWord_4127459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127459).length < 2 ^ (prefixWord ++ tailWord_4127459).sum := by decide
  have hdescent : baseEnd_4127459 < baseStart_4127459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127472 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_4127472 : Nat := 118140960795 + 4127472 * 2 ^ 59
def prefixEnd_4127472 : Nat := 4983230072969 + 3 ^ 40 * 4127472 * 2
def baseEnd_4127472 : Nat := 1412918015982920320345405

theorem tailTrace_4127472 : CollatzResearch.WordTrace tailWord_4127472 prefixEnd_4127472 1412918015982920320345405 := by
  unfold tailWord_4127472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270635651440667470736335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100360847535254223294315113 75270635651440667470736335)
  ·
    refine ⟨112905953477161001206104503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75270635651440667470736335 112905953477161001206104503)
    ·
      refine ⟨169358930215741501809156755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112905953477161001206104503 169358930215741501809156755)
      ·
        refine ⟨254038395323612252713735133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169358930215741501809156755 254038395323612252713735133)
        ·
          refine ⟨95264398246354594767650675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254038395323612252713735133 95264398246354594767650675)
          ·
            refine ⟨142896597369531892151476013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95264398246354594767650675 142896597369531892151476013)
            ·
              refine ⟨53586224013574459556803505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142896597369531892151476013 53586224013574459556803505)
              ·
                refine ⟨40189668010180844667602629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53586224013574459556803505 40189668010180844667602629)
                ·
                  refine ⟨7535562751908908375175493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40189668010180844667602629 7535562751908908375175493)
                  ·
                    refine ⟨1412918015982920320345405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535562751908908375175493 1412918015982920320345405)
                    ·
                      rfl

theorem cell22_4127472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_4127472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127472 prefixEnd_4127472 := by exact prefixLift 4127472
  have htrace : WordTrace (prefixWord ++ tailWord_4127472) baseStart_4127472 baseEnd_4127472 := by
    simpa [prefixWord, tailWord_4127472, baseEnd_4127472] using wordTrace_append hprefix tailTrace_4127472
  have hstable : (prefixWord ++ tailWord_4127472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127472).length < 2 ^ (prefixWord ++ tailWord_4127472).sum := by decide
  have hdescent : baseEnd_4127472 < baseStart_4127472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127540 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4127540 : Nat := 118140960795 + 4127540 * 2 ^ 59
def prefixEnd_4127540 : Nat := 4983230072969 + 3 ^ 40 * 4127540 * 2
def baseEnd_4127540 : Nat := 1412941293772590809645197

theorem tailTrace_4127540 : CollatzResearch.WordTrace tailWord_4127540 prefixEnd_4127540 1412941293772590809645197 := by
  unfold tailWord_4127540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75271875733317491277474037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100362500977756655036632049 75271875733317491277474037)
  ·
    refine ⟨7056738349998514807263191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75271875733317491277474037 7056738349998514807263191)
    ·
      refine ⟨10585107524997772210894787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056738349998514807263191 10585107524997772210894787)
      ·
        refine ⟨15877661287496658316342181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10585107524997772210894787 15877661287496658316342181)
        ·
          refine ⟨2977061491405623434314159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15877661287496658316342181 2977061491405623434314159)
          ·
            refine ⟨4465592237108435151471239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977061491405623434314159 4465592237108435151471239)
            ·
              refine ⟨6698388355662652727206859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465592237108435151471239 6698388355662652727206859)
              ·
                refine ⟨10047582533493979090810289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698388355662652727206859 10047582533493979090810289)
                ·
                  refine ⟨7535686900120484318107717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10047582533493979090810289 7535686900120484318107717)
                  ·
                    refine ⟨1412941293772590809645197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535686900120484318107717 1412941293772590809645197)
                    ·
                      rfl

theorem cell22_4127540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4127540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127540 prefixEnd_4127540 := by exact prefixLift 4127540
  have htrace : WordTrace (prefixWord ++ tailWord_4127540) baseStart_4127540 baseEnd_4127540 := by
    simpa [prefixWord, tailWord_4127540, baseEnd_4127540] using wordTrace_append hprefix tailTrace_4127540
  have hstable : (prefixWord ++ tailWord_4127540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127540).length < 2 ^ (prefixWord ++ tailWord_4127540).sum := by decide
  have hdescent : baseEnd_4127540 < baseStart_4127540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127564 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_4127564 : Nat := 118140960795 + 4127564 * 2 ^ 59
def prefixEnd_4127564 : Nat := 4983230072969 + 3 ^ 40 * 4127564 * 2
def baseEnd_4127564 : Nat := 1412949509463062747045123

theorem tailTrace_4127564 : CollatzResearch.WordTrace tailWord_4127564 prefixEnd_4127564 1412949509463062747045123 := by
  unfold tailWord_4127564
  simp only [CollatzResearch.WordTrace]
  refine ⟨75272313409274017326910873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100363084545698689769214497 75272313409274017326910873)
  ·
    refine ⟨56454235056955512995183155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75272313409274017326910873 56454235056955512995183155)
    ·
      refine ⟨84681352585433269492774733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56454235056955512995183155 84681352585433269492774733)
      ·
        refine ⟨31755507219537476059790525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84681352585433269492774733 31755507219537476059790525)
        ·
          refine ⟨11908315207326553522421447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31755507219537476059790525 11908315207326553522421447)
          ·
            refine ⟨17862472810989830283632171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908315207326553522421447 17862472810989830283632171)
            ·
              refine ⟨26793709216484745425448257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17862472810989830283632171 26793709216484745425448257)
              ·
                refine ⟨20095281912363559069086193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26793709216484745425448257 20095281912363559069086193)
                ·
                  refine ⟨15071461434272669301814645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20095281912363559069086193 15071461434272669301814645)
                  ·
                    refine ⟨1412949509463062747045123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15071461434272669301814645 1412949509463062747045123)
                    ·
                      rfl

theorem cell22_4127564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_4127564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127564 prefixEnd_4127564 := by exact prefixLift 4127564
  have htrace : WordTrace (prefixWord ++ tailWord_4127564) baseStart_4127564 baseEnd_4127564 := by
    simpa [prefixWord, tailWord_4127564, baseEnd_4127564] using wordTrace_append hprefix tailTrace_4127564
  have hstable : (prefixWord ++ tailWord_4127564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127564).length < 2 ^ (prefixWord ++ tailWord_4127564).sum := by decide
  have hdescent : baseEnd_4127564 < baseStart_4127564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127596 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_4127596 : Nat := 118140960795 + 4127596 * 2 ^ 59
def prefixEnd_4127596 : Nat := 4983230072969 + 3 ^ 40 * 4127596 * 2
def baseEnd_4127596 : Nat := 1412960463717025330245025

theorem tailTrace_4127596 : CollatzResearch.WordTrace tailWord_4127596 prefixEnd_4127596 1412960463717025330245025 := by
  unfold tailWord_4127596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75272896977216052059493321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100363862636288069412657761 75272896977216052059493321)
  ·
    refine ⟨56454672732912039044619991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75272896977216052059493321 56454672732912039044619991)
    ·
      refine ⟨84682009099368058566929987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56454672732912039044619991 84682009099368058566929987)
      ·
        refine ⟨127023013649052087850394981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84682009099368058566929987 127023013649052087850394981)
        ·
          refine ⟨23816815059197266471949059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127023013649052087850394981 23816815059197266471949059)
          ·
            refine ⟨35725222588795899707923589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23816815059197266471949059 35725222588795899707923589)
            ·
              refine ⟨6698479235399231195235673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35725222588795899707923589 6698479235399231195235673)
              ·
                refine ⟨5023859426549423396426755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6698479235399231195235673 5023859426549423396426755)
                ·
                  refine ⟨7535789139824135094640133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023859426549423396426755 7535789139824135094640133)
                  ·
                    refine ⟨1412960463717025330245025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7535789139824135094640133 1412960463717025330245025)
                    ·
                      rfl

theorem cell22_4127596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_4127596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127596 prefixEnd_4127596 := by exact prefixLift 4127596
  have htrace : WordTrace (prefixWord ++ tailWord_4127596) baseStart_4127596 baseEnd_4127596 := by
    simpa [prefixWord, tailWord_4127596, baseEnd_4127596] using wordTrace_append hprefix tailTrace_4127596
  have hstable : (prefixWord ++ tailWord_4127596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127596).length < 2 ^ (prefixWord ++ tailWord_4127596).sum := by decide
  have hdescent : baseEnd_4127596 < baseStart_4127596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127611 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 4]
def baseStart_4127611 : Nat := 118140960795 + 4127611 * 2 ^ 59
def prefixEnd_4127611 : Nat := 4983230072969 + 3 ^ 40 * 4127611 * 2
def baseEnd_4127611 : Nat := 470988532841190097039993

theorem tailTrace_4127611 : CollatzResearch.WordTrace tailWord_4127611 prefixEnd_4127611 470988532841190097039993 := by
  unfold tailWord_4127611
  simp only [CollatzResearch.WordTrace]
  refine ⟨150546341049377761680782687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100364227366251841120521791 150546341049377761680782687)
  ·
    refine ⟨225819511574066642521174031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150546341049377761680782687 225819511574066642521174031)
    ·
      refine ⟨338729267361099963781761047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225819511574066642521174031 338729267361099963781761047)
      ·
        refine ⟨508093901041649945672641571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338729267361099963781761047 508093901041649945672641571)
        ·
          refine ⟨762140851562474918508962357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508093901041649945672641571 762140851562474918508962357)
          ·
            refine ⟨71450704833982023610215221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 762140851562474918508962357 71450704833982023610215221)
            ·
              refine ⟨6698503578185814713457677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71450704833982023610215221 6698503578185814713457677)
              ·
                refine ⟨2511938841819680517546629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698503578185814713457677 2511938841819680517546629)
                ·
                  refine ⟨470988532841190097039993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511938841819680517546629 470988532841190097039993)
                  ·
                    rfl

theorem cell22_4127611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 4].length) (baseStart_4127611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127611 prefixEnd_4127611 := by exact prefixLift 4127611
  have htrace : WordTrace (prefixWord ++ tailWord_4127611) baseStart_4127611 baseEnd_4127611 := by
    simpa [prefixWord, tailWord_4127611, baseEnd_4127611] using wordTrace_append hprefix tailTrace_4127611
  have hstable : (prefixWord ++ tailWord_4127611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127611).length < 2 ^ (prefixWord ++ tailWord_4127611).sum := by decide
  have hdescent : baseEnd_4127611 < baseStart_4127611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127639 : List Nat := [1, 1, 3, 3, 1, 2, 4, 7]
def baseStart_4127639 : Nat := 118140960795 + 4127639 * 2 ^ 59
def prefixEnd_4127639 : Nat := 4983230072969 + 3 ^ 40 * 4127639 * 2
def baseEnd_4127639 : Nat := 156997242610643061268877

theorem tailTrace_4127639 : CollatzResearch.WordTrace tailWord_4127639 prefixEnd_4127639 156997242610643061268877 := by
  unfold tailWord_4127639
  simp only [CollatzResearch.WordTrace]
  refine ⟨150547362293276322462801971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100364908195517548308534647 150547362293276322462801971)
  ·
    refine ⟨225821043439914483694202957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150547362293276322462801971 225821043439914483694202957)
    ·
      refine ⟨84682891289967931385326109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225821043439914483694202957 84682891289967931385326109)
      ·
        refine ⟨31756084233737974269497291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84682891289967931385326109 31756084233737974269497291)
        ·
          refine ⟨47634126350606961404245937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31756084233737974269497291 47634126350606961404245937)
          ·
            refine ⟨35725594762955221053184453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47634126350606961404245937 35725594762955221053184453)
            ·
              refine ⟨6698549018054103947472085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35725594762955221053184453 6698549018054103947472085)
              ·
                refine ⟨156997242610643061268877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6698549018054103947472085 156997242610643061268877)
                ·
                  rfl

theorem cell22_4127639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 7].length) (baseStart_4127639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127639 prefixEnd_4127639 := by exact prefixLift 4127639
  have htrace : WordTrace (prefixWord ++ tailWord_4127639) baseStart_4127639 baseEnd_4127639 := by
    simpa [prefixWord, tailWord_4127639, baseEnd_4127639] using wordTrace_append hprefix tailTrace_4127639
  have hstable : (prefixWord ++ tailWord_4127639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127639).length < 2 ^ (prefixWord ++ tailWord_4127639).sum := by decide
  have hdescent : baseEnd_4127639 < baseStart_4127639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127778 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_4127778 : Nat := 118140960795 + 4127778 * 2 ^ 59
def prefixEnd_4127778 : Nat := 4983230072969 + 3 ^ 40 * 4127778 * 2
def baseEnd_4127778 : Nat := 1413022766036437522194467

theorem tailTrace_4127778 : CollatzResearch.WordTrace tailWord_4127778 prefixEnd_4127778 1413022766036437522194467 := by
  unfold tailWord_4127778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37638108009943187300527997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100368288026515166134741325 37638108009943187300527997)
  ·
    refine ⟨14114290503728695237697999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37638108009943187300527997 14114290503728695237697999)
    ·
      refine ⟨21171435755593042856546999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114290503728695237697999 21171435755593042856546999)
      ·
        refine ⟨31757153633389564284820499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21171435755593042856546999 31757153633389564284820499)
        ·
          refine ⟨47635730450084346427230749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31757153633389564284820499 47635730450084346427230749)
          ·
            refine ⟨17863398918781629910211531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47635730450084346427230749 17863398918781629910211531)
            ·
              refine ⟨26795098378172444865317297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863398918781629910211531 26795098378172444865317297)
              ·
                refine ⟨20096323783629333648987973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26795098378172444865317297 20096323783629333648987973)
                ·
                  refine ⟨3768060709430500059185245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20096323783629333648987973 3768060709430500059185245)
                  ·
                    refine ⟨1413022766036437522194467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768060709430500059185245 1413022766036437522194467)
                    ·
                      rfl

theorem cell22_4127778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_4127778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127778 prefixEnd_4127778 := by exact prefixLift 4127778
  have htrace : WordTrace (prefixWord ++ tailWord_4127778) baseStart_4127778 baseEnd_4127778 := by
    simpa [prefixWord, tailWord_4127778, baseEnd_4127778] using wordTrace_append hprefix tailTrace_4127778
  have hstable : (prefixWord ++ tailWord_4127778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127778).length < 2 ^ (prefixWord ++ tailWord_4127778).sum := by decide
  have hdescent : baseEnd_4127778 < baseStart_4127778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127780 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_4127780 : Nat := 118140960795 + 4127780 * 2 ^ 59
def prefixEnd_4127780 : Nat := 4983230072969 + 3 ^ 40 * 4127780 * 2
def baseEnd_4127780 : Nat := 471007816892436727881487

theorem tailTrace_4127780 : CollatzResearch.WordTrace tailWord_4127780 prefixEnd_4127780 471007816892436727881487 := by
  unfold tailWord_4127780
  simp only [CollatzResearch.WordTrace]
  refine ⟨75276252492882751771842397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100368336657177002362456529 75276252492882751771842397)
  ·
    refine ⟨28228594684831031914440899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75276252492882751771842397 28228594684831031914440899)
    ·
      refine ⟨42342892027246547871661349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28228594684831031914440899 42342892027246547871661349)
      ·
        refine ⟨7939292255108727725936503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42342892027246547871661349 7939292255108727725936503)
        ·
          refine ⟨11908938382663091588904755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939292255108727725936503 11908938382663091588904755)
          ·
            refine ⟨17863407573994637383357133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908938382663091588904755 17863407573994637383357133)
            ·
              refine ⟨6698777840247989018758925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17863407573994637383357133 6698777840247989018758925)
              ·
                refine ⟨2512041690092995882034597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698777840247989018758925 2512041690092995882034597)
                ·
                  refine ⟨471007816892436727881487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2512041690092995882034597 471007816892436727881487)
                  ·
                    rfl

theorem cell22_4127780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_4127780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127780 prefixEnd_4127780 := by exact prefixLift 4127780
  have htrace : WordTrace (prefixWord ++ tailWord_4127780) baseStart_4127780 baseEnd_4127780 := by
    simpa [prefixWord, tailWord_4127780, baseEnd_4127780] using wordTrace_append hprefix tailTrace_4127780
  have hstable : (prefixWord ++ tailWord_4127780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127780).length < 2 ^ (prefixWord ++ tailWord_4127780).sum := by decide
  have hdescent : baseEnd_4127780 < baseStart_4127780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127840 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_4127840 : Nat := 118140960795 + 4127840 * 2 ^ 59
def prefixEnd_4127840 : Nat := 4983230072969 + 3 ^ 40 * 4127840 * 2
def baseEnd_4127840 : Nat := 1413043989903490027144277

theorem tailTrace_4127840 : CollatzResearch.WordTrace tailWord_4127840 prefixEnd_4127840 1413043989903490027144277 := by
  unfold tailWord_4127840
  simp only [CollatzResearch.WordTrace]
  refine ⟨75277346682774066895434487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100369795577032089193912649 75277346682774066895434487)
  ·
    refine ⟨112916020024161100343151731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75277346682774066895434487 112916020024161100343151731)
    ·
      refine ⟨169374030036241650514727597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112916020024161100343151731 169374030036241650514727597)
      ·
        refine ⟨63515261263590618943022849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169374030036241650514727597 63515261263590618943022849)
        ·
          refine ⟨47636445947692964207267137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63515261263590618943022849 47636445947692964207267137)
          ·
            refine ⟨35727334460769723155450353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47636445947692964207267137 35727334460769723155450353)
            ·
              refine ⟨26795500845577292366587765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35727334460769723155450353 26795500845577292366587765)
              ·
                refine ⟨2512078204272871159367603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26795500845577292366587765 2512078204272871159367603)
                ·
                  refine ⟨3768117306409306739051405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512078204272871159367603 3768117306409306739051405)
                  ·
                    refine ⟨1413043989903490027144277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768117306409306739051405 1413043989903490027144277)
                    ·
                      rfl

theorem cell22_4127840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_4127840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127840 prefixEnd_4127840 := by exact prefixLift 4127840
  have htrace : WordTrace (prefixWord ++ tailWord_4127840) baseStart_4127840 baseEnd_4127840 := by
    simpa [prefixWord, tailWord_4127840, baseEnd_4127840] using wordTrace_append hprefix tailTrace_4127840
  have hstable : (prefixWord ++ tailWord_4127840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127840).length < 2 ^ (prefixWord ++ tailWord_4127840).sum := by decide
  have hdescent : baseEnd_4127840 < baseStart_4127840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127853 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4127853 : Nat := 118140960795 + 4127853 * 2 ^ 59
def prefixEnd_4127853 : Nat := 4983230072969 + 3 ^ 40 * 4127853 * 2
def baseEnd_4127853 : Nat := 471016146689720775523079

theorem tailTrace_4127853 : CollatzResearch.WordTrace tailWord_4127853 prefixEnd_4127853 471016146689720775523079 := by
  unfold tailWord_4127853
  simp only [CollatzResearch.WordTrace]
  refine ⟨150555167514501037011092213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100370111676334024674061475 150555167514501037011092213)
  ·
    refine ⟨14114546954484472219789895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150555167514501037011092213 14114546954484472219789895)
    ·
      refine ⟨21171820431726708329684843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114546954484472219789895 21171820431726708329684843)
      ·
        refine ⟨31757730647590062494527265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21171820431726708329684843 31757730647590062494527265)
        ·
          refine ⟨23818297985692546870895449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31757730647590062494527265 23818297985692546870895449)
          ·
            refine ⟨17863723489269410153171587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23818297985692546870895449 17863723489269410153171587)
            ·
              refine ⟨26795585233904115229757381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863723489269410153171587 26795585233904115229757381)
              ·
                refine ⟨5024172231357021605579509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26795585233904115229757381 5024172231357021605579509)
                ·
                  refine ⟨471016146689720775523079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024172231357021605579509 471016146689720775523079)
                  ·
                    rfl

theorem cell22_4127853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4127853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127853 prefixEnd_4127853 := by exact prefixLift 4127853
  have htrace : WordTrace (prefixWord ++ tailWord_4127853) baseStart_4127853 baseEnd_4127853 := by
    simpa [prefixWord, tailWord_4127853, baseEnd_4127853] using wordTrace_append hprefix tailTrace_4127853
  have hstable : (prefixWord ++ tailWord_4127853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127853).length < 2 ^ (prefixWord ++ tailWord_4127853).sum := by decide
  have hdescent : baseEnd_4127853 < baseStart_4127853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127881 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 8]
def baseStart_4127881 : Nat := 118140960795 + 4127881 * 2 ^ 59
def prefixEnd_4127881 : Nat := 4983230072969 + 3 ^ 40 * 4127881 * 2
def baseEnd_4127881 : Nat := 471019341680459862289717

theorem tailTrace_4127881 : CollatzResearch.WordTrace tailWord_4127881 prefixEnd_4127881 471019341680459862289717 := by
  unfold tailWord_4127881
  simp only [CollatzResearch.WordTrace]
  refine ⟨150556188758399597793111497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100370792505599731862074331 150556188758399597793111497)
  ·
    refine ⟨112917141568799698344833623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150556188758399597793111497 112917141568799698344833623)
    ·
      refine ⟨169375712353199547517250435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112917141568799698344833623 169375712353199547517250435)
      ·
        refine ⟨254063568529799321275875653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169375712353199547517250435 254063568529799321275875653)
        ·
          refine ⟨47636919099337372739226685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254063568529799321275875653 47636919099337372739226685)
          ·
            refine ⟨17863844662251514777210007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47636919099337372739226685 17863844662251514777210007)
            ·
              refine ⟨26795766993377272165815011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17863844662251514777210007 26795766993377272165815011)
              ·
                refine ⟨40193650490065908248722517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26795766993377272165815011 40193650490065908248722517)
                ·
                  refine ⟨471019341680459862289717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40193650490065908248722517 471019341680459862289717)
                  ·
                    rfl

theorem cell22_4127881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_4127881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127881 prefixEnd_4127881 := by exact prefixLift 4127881
  have htrace : WordTrace (prefixWord ++ tailWord_4127881) baseStart_4127881 baseEnd_4127881 := by
    simpa [prefixWord, tailWord_4127881, baseEnd_4127881] using wordTrace_append hprefix tailTrace_4127881
  have hstable : (prefixWord ++ tailWord_4127881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127881).length < 2 ^ (prefixWord ++ tailWord_4127881).sum := by decide
  have hdescent : baseEnd_4127881 < baseStart_4127881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127900 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4127900 : Nat := 118140960795 + 4127900 * 2 ^ 59
def prefixEnd_4127900 : Nat := 4983230072969 + 3 ^ 40 * 4127900 * 2
def baseEnd_4127900 : Nat := 1413064529129669870644093

theorem tailTrace_4127900 : CollatzResearch.WordTrace tailWord_4127900 prefixEnd_4127900 1413064529129669870644093 := by
  unfold tailWord_4127900
  simp only [CollatzResearch.WordTrace]
  refine ⟨75278440872665382019026577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100371254496887176025368769 75278440872665382019026577)
  ·
    refine ⟨56458830654499036514269933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75278440872665382019026577 56458830654499036514269933)
    ·
      refine ⟨21172061495437138692851225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56458830654499036514269933 21172061495437138692851225)
      ·
        refine ⟨15879046121577854019638419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21172061495437138692851225 15879046121577854019638419)
        ·
          refine ⟨23818569182366781029457629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879046121577854019638419 23818569182366781029457629)
          ·
            refine ⟨8931963443387542886046611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23818569182366781029457629 8931963443387542886046611)
            ·
              refine ⟨13397945165081314329069917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931963443387542886046611 13397945165081314329069917)
              ·
                refine ⟨5024229436905492873401219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13397945165081314329069917 5024229436905492873401219)
                ·
                  refine ⟨7536344155358239310101829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024229436905492873401219 7536344155358239310101829)
                  ·
                    refine ⟨1413064529129669870644093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536344155358239310101829 1413064529129669870644093)
                    ·
                      rfl

theorem cell22_4127900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4127900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127900 prefixEnd_4127900 := by exact prefixLift 4127900
  have htrace : WordTrace (prefixWord ++ tailWord_4127900) baseStart_4127900 baseEnd_4127900 := by
    simpa [prefixWord, tailWord_4127900, baseEnd_4127900] using wordTrace_append hprefix tailTrace_4127900
  have hstable : (prefixWord ++ tailWord_4127900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127900).length < 2 ^ (prefixWord ++ tailWord_4127900).sum := by decide
  have hdescent : baseEnd_4127900 < baseStart_4127900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127941 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_4127941 : Nat := 118140960795 + 4127941 * 2 ^ 59
def prefixEnd_4127941 : Nat := 4983230072969 + 3 ^ 40 * 4127941 * 2
def baseEnd_4127941 : Nat := 1413078564267559430368967

theorem tailTrace_4127941 : CollatzResearch.WordTrace tailWord_4127941 prefixEnd_4127941 1413078564267559430368967 := by
  unfold tailWord_4127941
  simp only [CollatzResearch.WordTrace]
  refine ⟨150558377138182228040295677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100372251425454818693530451 150558377138182228040295677)
  ·
    refine ⟨56459391426818335515110879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150558377138182228040295677 56459391426818335515110879)
    ·
      refine ⟨84689087140227503272666319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56459391426818335515110879 84689087140227503272666319)
      ·
        refine ⟨127033630710341254908999479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84689087140227503272666319 127033630710341254908999479)
        ·
          refine ⟨190550446065511882363499219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127033630710341254908999479 190550446065511882363499219)
          ·
            refine ⟨285825669098267823545248829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190550446065511882363499219 285825669098267823545248829)
            ·
              refine ⟨107184625911850433829468311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285825669098267823545248829 107184625911850433829468311)
              ·
                refine ⟨160776938867775650744202467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107184625911850433829468311 160776938867775650744202467)
                ·
                  refine ⟨241165408301663476116303701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160776938867775650744202467 241165408301663476116303701)
                  ·
                    refine ⟨1413078564267559430368967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241165408301663476116303701 1413078564267559430368967)
                    ·
                      rfl

theorem cell22_4127941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_4127941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127941 prefixEnd_4127941 := by exact prefixLift 4127941
  have htrace : WordTrace (prefixWord ++ tailWord_4127941) baseStart_4127941 baseEnd_4127941 := by
    simpa [prefixWord, tailWord_4127941, baseEnd_4127941] using wordTrace_append hprefix tailTrace_4127941
  have hstable : (prefixWord ++ tailWord_4127941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127941).length < 2 ^ (prefixWord ++ tailWord_4127941).sum := by decide
  have hdescent : baseEnd_4127941 < baseStart_4127941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
