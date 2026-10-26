import V185TrunkScan23Chunk0241

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1431243 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4]
def baseStart_1431243 : Nat := 118140960795 + 1431243 * 2 ^ 59
def prefixEnd_1431243 : Nat := 4983230072969 + 3 ^ 40 * 1431243 * 2
def baseEnd_1431243 : Nat := 734915592383048988880339

theorem tailTrace_1431243 : CollatzResearch.WordTrace tailWord_1431243 prefixEnd_1431243 734915592383048988880339 := by
  unfold tailWord_1431243
  simp only [CollatzResearch.WordTrace]
  refine ⟨52201720753858522688898383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34801147169239015125932255 52201720753858522688898383)
  ·
    refine ⟨78302581130787784033347575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52201720753858522688898383 78302581130787784033347575)
    ·
      refine ⟨117453871696181676050021363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78302581130787784033347575 117453871696181676050021363)
      ·
        refine ⟨176180807544272514075032045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117453871696181676050021363 176180807544272514075032045)
        ·
          refine ⟨66067802829102192778137017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176180807544272514075032045 66067802829102192778137017)
          ·
            refine ⟨49550852121826644583602763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66067802829102192778137017 49550852121826644583602763)
            ·
              refine ⟨74326278182739966875404145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49550852121826644583602763 74326278182739966875404145)
              ·
                refine ⟨55744708637054975156553109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74326278182739966875404145 55744708637054975156553109)
                ·
                  refine ⟨2613033217361951960463427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55744708637054975156553109 2613033217361951960463427)
                  ·
                    refine ⟨3919549826042927940695141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613033217361951960463427 3919549826042927940695141)
                    ·
                      refine ⟨734915592383048988880339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3919549826042927940695141 734915592383048988880339)
                      ·
                        rfl

theorem cell23_1431243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_1431243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431243 prefixEnd_1431243 := by exact prefixLift 1431243
  have htrace : WordTrace (prefixWord ++ tailWord_1431243) baseStart_1431243 baseEnd_1431243 := by
    simpa [prefixWord, tailWord_1431243, baseEnd_1431243] using wordTrace_append hprefix tailTrace_1431243
  have hstable : (prefixWord ++ tailWord_1431243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431243).length < 2 ^ (prefixWord ++ tailWord_1431243).sum := by decide
  have hdescent : baseEnd_1431243 < baseStart_1431243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431244 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 5]
def baseStart_1431244 : Nat := 118140960795 + 1431244 * 2 ^ 59
def prefixEnd_1431244 : Nat := 4983230072969 + 3 ^ 40 * 1431244 * 2
def baseEnd_1431244 : Nat := 81657345095967053885315

theorem tailTrace_1431244 : CollatzResearch.WordTrace tailWord_1431244 prefixEnd_1431244 81657345095967053885315 := by
  unfold tailWord_1431244
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100878613427449929842393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34801171484569933239789857 26100878613427449929842393)
  ·
    refine ⟨19575658960070587447381795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26100878613427449929842393 19575658960070587447381795)
    ·
      refine ⟨29363488440105881171072693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19575658960070587447381795 29363488440105881171072693)
      ·
        refine ⟨2752827041259926359788065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29363488440105881171072693 2752827041259926359788065)
        ·
          refine ⟨2064620280944944769841049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752827041259926359788065 2064620280944944769841049)
          ·
            refine ⟨1548465210708708577380787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064620280944944769841049 1548465210708708577380787)
            ·
              refine ⟨2322697816063062866071181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548465210708708577380787 2322697816063062866071181)
              ·
                refine ⟨871011681023648574776693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322697816063062866071181 871011681023648574776693)
                ·
                  refine ⟨81657345095967053885315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871011681023648574776693 81657345095967053885315)
                  ·
                    rfl

theorem cell23_1431244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_1431244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431244 prefixEnd_1431244 := by exact prefixLift 1431244
  have htrace : WordTrace (prefixWord ++ tailWord_1431244) baseStart_1431244 baseEnd_1431244 := by
    simpa [prefixWord, tailWord_1431244, baseEnd_1431244] using wordTrace_append hprefix tailTrace_1431244
  have hstable : (prefixWord ++ tailWord_1431244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431244).length < 2 ^ (prefixWord ++ tailWord_1431244).sum := by decide
  have hdescent : baseEnd_1431244 < baseStart_1431244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431261 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 5]
def baseStart_1431261 : Nat := 118140960795 + 1431261 * 2 ^ 59
def prefixEnd_1431261 : Nat := 4983230072969 + 3 ^ 40 * 1431261 * 2
def baseEnd_1431261 : Nat := 81658315003869990939473

theorem tailTrace_1431261 : CollatzResearch.WordTrace tailWord_1431261 prefixEnd_1431261 81658315003869990939473 := by
  unfold tailWord_1431261
  simp only [CollatzResearch.WordTrace]
  refine ⟨52202377267793311763053637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34801584845195541175369091 52202377267793311763053637)
  ·
    refine ⟨9787945737711245955572557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52202377267793311763053637 9787945737711245955572557)
    ·
      refine ⟨3670479651641717233339709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9787945737711245955572557 3670479651641717233339709)
      ·
        refine ⟨1376429869365643962502391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3670479651641717233339709 1376429869365643962502391)
        ·
          refine ⟨2064644804048465943753587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376429869365643962502391 2064644804048465943753587)
          ·
            refine ⟨3096967206072698915630381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064644804048465943753587 3096967206072698915630381)
            ·
              refine ⟨1161362702277262093361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3096967206072698915630381 1161362702277262093361393)
              ·
                refine ⟨871022026707946570021045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161362702277262093361393 871022026707946570021045)
                ·
                  refine ⟨81658315003869990939473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871022026707946570021045 81658315003869990939473)
                  ·
                    rfl

theorem cell23_1431261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_1431261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431261 prefixEnd_1431261 := by exact prefixLift 1431261
  have htrace : WordTrace (prefixWord ++ tailWord_1431261) baseStart_1431261 baseEnd_1431261 := by
    simpa [prefixWord, tailWord_1431261, baseEnd_1431261] using wordTrace_append hprefix tailTrace_1431261
  have hstable : (prefixWord ++ tailWord_1431261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431261).length < 2 ^ (prefixWord ++ tailWord_1431261).sum := by decide
  have hdescent : baseEnd_1431261 < baseStart_1431261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431294 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1431294 : Nat := 118140960795 + 1431294 * 2 ^ 59
def prefixEnd_1431294 : Nat := 4983230072969 + 3 ^ 40 * 1431294 * 2
def baseEnd_1431294 : Nat := 734941779896428289342605

theorem tailTrace_1431294 : CollatzResearch.WordTrace tailWord_1431294 prefixEnd_1431294 734941779896428289342605 := by
  unfold tailWord_1431294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6525447609584219799875617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34802387251115838932669957 6525447609584219799875617)
  ·
    refine ⟨4894085707188164849906713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6525447609584219799875617 4894085707188164849906713)
    ·
      refine ⟨3670564280391123637430035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894085707188164849906713 3670564280391123637430035)
      ·
        refine ⟨5505846420586685456145053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670564280391123637430035 5505846420586685456145053)
        ·
          refine ⟨2064692407720007046054395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5505846420586685456145053 2064692407720007046054395)
          ·
            refine ⟨3097038611580010569081593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064692407720007046054395 3097038611580010569081593)
            ·
              refine ⟨2322778958685007926811195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097038611580010569081593 2322778958685007926811195)
              ·
                refine ⟨3484168438027511890216793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322778958685007926811195 3484168438027511890216793)
                ·
                  refine ⟨2613126328520633917662595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484168438027511890216793 2613126328520633917662595)
                  ·
                    refine ⟨3919689492780950876493893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613126328520633917662595 3919689492780950876493893)
                    ·
                      refine ⟨734941779896428289342605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3919689492780950876493893 734941779896428289342605)
                      ·
                        rfl

theorem cell23_1431294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1431294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431294 prefixEnd_1431294 := by exact prefixLift 1431294
  have htrace : WordTrace (prefixWord ++ tailWord_1431294) baseStart_1431294 baseEnd_1431294 := by
    simpa [prefixWord, tailWord_1431294, baseEnd_1431294] using wordTrace_append hprefix tailTrace_1431294
  have hstable : (prefixWord ++ tailWord_1431294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431294).length < 2 ^ (prefixWord ++ tailWord_1431294).sum := by decide
  have hdescent : baseEnd_1431294 < baseStart_1431294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431314 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1431314 : Nat := 118140960795 + 1431314 * 2 ^ 59
def prefixEnd_1431314 : Nat := 4983230072969 + 3 ^ 40 * 1431314 * 2
def baseEnd_1431314 : Nat := 734952049509518211092513

theorem tailTrace_1431314 : CollatzResearch.WordTrace tailWord_1431314 prefixEnd_1431314 734952049509518211092513 := by
  unfold tailWord_1431314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051077584150325453683249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34802873557734201209821997 13051077584150325453683249)
  ·
    refine ⟨9788308188112744090262437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13051077584150325453683249 9788308188112744090262437)
    ·
      refine ⟨1835307785271139516924207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9788308188112744090262437 1835307785271139516924207)
      ·
        refine ⟨2752961677906709275386311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835307785271139516924207 2752961677906709275386311)
        ·
          refine ⟨4129442516860063913079467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752961677906709275386311 4129442516860063913079467)
          ·
            refine ⟨6194163775290095869619201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129442516860063913079467 6194163775290095869619201)
            ·
              refine ⟨4645622831467571902214401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194163775290095869619201 4645622831467571902214401)
              ·
                refine ⟨3484217123600678926660801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645622831467571902214401 3484217123600678926660801)
                ·
                  refine ⟨2613162842700509194995601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484217123600678926660801 2613162842700509194995601)
                  ·
                    refine ⟨1959872132025381896246701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613162842700509194995601 1959872132025381896246701)
                    ·
                      refine ⟨734952049509518211092513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959872132025381896246701 734952049509518211092513)
                      ·
                        rfl

theorem cell23_1431314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1431314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431314 prefixEnd_1431314 := by exact prefixLift 1431314
  have htrace : WordTrace (prefixWord ++ tailWord_1431314) baseStart_1431314 baseEnd_1431314 := by
    simpa [prefixWord, tailWord_1431314, baseEnd_1431314] using wordTrace_append hprefix tailTrace_1431314
  have hstable : (prefixWord ++ tailWord_1431314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431314).length < 2 ^ (prefixWord ++ tailWord_1431314).sum := by decide
  have hdescent : baseEnd_1431314 < baseStart_1431314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431327 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1431327 : Nat := 118140960795 + 1431327 * 2 ^ 59
def prefixEnd_1431327 : Nat := 4983230072969 + 3 ^ 40 * 1431327 * 2
def baseEnd_1431327 : Nat := 734958724758026660229953

theorem tailTrace_1431327 : CollatzResearch.WordTrace tailWord_1431327 prefixEnd_1431327 734958724758026660229953 := by
  unfold tailWord_1431327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52204784485554205034956235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34803189657036136689970823 52204784485554205034956235)
  ·
    refine ⟨78307176728331307552434353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52204784485554205034956235 78307176728331307552434353)
    ·
      refine ⟨58730382546248480664325765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78307176728331307552434353 58730382546248480664325765)
      ·
        refine ⟨11011946727421590124561081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58730382546248480664325765 11011946727421590124561081)
        ·
          refine ⟨8258960045566192593420811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011946727421590124561081 8258960045566192593420811)
          ·
            refine ⟨12388440068349288890131217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258960045566192593420811 12388440068349288890131217)
            ·
              refine ⟨9291330051261966667598413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12388440068349288890131217 9291330051261966667598413)
              ·
                refine ⟨3484248769223237500349405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9291330051261966667598413 3484248769223237500349405)
                ·
                  refine ⟨1306593288458714062631027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3484248769223237500349405 1306593288458714062631027)
                  ·
                    refine ⟨1959889932688071093946541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1306593288458714062631027 1959889932688071093946541)
                    ·
                      refine ⟨734958724758026660229953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959889932688071093946541 734958724758026660229953)
                      ·
                        rfl

theorem cell23_1431327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1431327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431327 prefixEnd_1431327 := by exact prefixLift 1431327
  have htrace : WordTrace (prefixWord ++ tailWord_1431327) baseStart_1431327 baseEnd_1431327 := by
    simpa [prefixWord, tailWord_1431327, baseEnd_1431327] using wordTrace_append hprefix tailTrace_1431327
  have hstable : (prefixWord ++ tailWord_1431327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431327).length < 2 ^ (prefixWord ++ tailWord_1431327).sum := by decide
  have hdescent : baseEnd_1431327 < baseStart_1431327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431330 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1431330 : Nat := 118140960795 + 1431330 * 2 ^ 59
def prefixEnd_1431330 : Nat := 4983230072969 + 3 ^ 40 * 1431330 * 2
def baseEnd_1431330 : Nat := 244986755066663382830813

theorem tailTrace_1431330 : CollatzResearch.WordTrace tailWord_1431330 prefixEnd_1431330 244986755066663382830813 := by
  unfold tailWord_1431330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051223476135834136828861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34803262603028891031543629 13051223476135834136828861)
  ·
    refine ⟨4894208803550937801310823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13051223476135834136828861 4894208803550937801310823)
    ·
      refine ⟨7341313205326406701966235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894208803550937801310823 7341313205326406701966235)
      ·
        refine ⟨11011969807989610052949353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7341313205326406701966235 11011969807989610052949353)
        ·
          refine ⟨8258977355992207539712015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011969807989610052949353 8258977355992207539712015)
          ·
            refine ⟨12388466033988311309568023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258977355992207539712015 12388466033988311309568023)
            ·
              refine ⟨18582699050982466964352035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12388466033988311309568023 18582699050982466964352035)
              ·
                refine ⟨27874048576473700446528053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18582699050982466964352035 27874048576473700446528053)
                ·
                  refine ⟨2613192054044409416862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27874048576473700446528053 2613192054044409416862005)
                  ·
                    refine ⟨244986755066663382830813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2613192054044409416862005 244986755066663382830813)
                    ·
                      rfl

theorem cell23_1431330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1431330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431330 prefixEnd_1431330 := by exact prefixLift 1431330
  have htrace : WordTrace (prefixWord ++ tailWord_1431330) baseStart_1431330 baseEnd_1431330 := by
    simpa [prefixWord, tailWord_1431330, baseEnd_1431330] using wordTrace_append hprefix tailTrace_1431330
  have hstable : (prefixWord ++ tailWord_1431330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431330).length < 2 ^ (prefixWord ++ tailWord_1431330).sum := by decide
  have hdescent : baseEnd_1431330 < baseStart_1431330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431343 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 6]
def baseStart_1431343 : Nat := 118140960795 + 1431343 * 2 ^ 59
def prefixEnd_1431343 : Nat := 4983230072969 + 3 ^ 40 * 1431343 * 2
def baseEnd_1431343 : Nat := 244988980149499532543293

theorem tailTrace_1431343 : CollatzResearch.WordTrace tailWord_1431343 prefixEnd_1431343 244988980149499532543293 := by
  unfold tailWord_1431343
  simp only [CollatzResearch.WordTrace]
  refine ⟨52205368053496239767538683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34803578702330826511692455 52205368053496239767538683)
  ·
    refine ⟨78308052080244359651308025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52205368053496239767538683 78308052080244359651308025)
    ·
      refine ⟨58731039060183269738481019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78308052080244359651308025 58731039060183269738481019)
      ·
        refine ⟨88096558590274904607721529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58731039060183269738481019 88096558590274904607721529)
        ·
          refine ⟨66072418942706178455791147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88096558590274904607721529 66072418942706178455791147)
          ·
            refine ⟨99108628414059267683686721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66072418942706178455791147 99108628414059267683686721)
            ·
              refine ⟨74331471310544450762765041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99108628414059267683686721 74331471310544450762765041)
              ·
                refine ⟨55748603482908338072073781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74331471310544450762765041 55748603482908338072073781)
                ·
                  refine ⟨5226431576522656694256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55748603482908338072073781 5226431576522656694256917)
                  ·
                    refine ⟨244988980149499532543293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5226431576522656694256917 244988980149499532543293)
                    ·
                      rfl

theorem cell23_1431343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_1431343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431343 prefixEnd_1431343 := by exact prefixLift 1431343
  have htrace : WordTrace (prefixWord ++ tailWord_1431343) baseStart_1431343 baseEnd_1431343 := by
    simpa [prefixWord, tailWord_1431343, baseEnd_1431343] using wordTrace_append hprefix tailTrace_1431343
  have hstable : (prefixWord ++ tailWord_1431343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431343).length < 2 ^ (prefixWord ++ tailWord_1431343).sum := by decide
  have hdescent : baseEnd_1431343 < baseStart_1431343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431354 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_1431354 : Nat := 118140960795 + 1431354 * 2 ^ 59
def prefixEnd_1431354 : Nat := 4983230072969 + 3 ^ 40 * 1431354 * 2
def baseEnd_1431354 : Nat := 734972588735698054592329

theorem tailTrace_1431354 : CollatzResearch.WordTrace tailWord_1431354 prefixEnd_1431354 734972588735698054592329 := by
  unfold tailWord_1431354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051442314114097161547279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34803846170970925764126077 13051442314114097161547279)
  ·
    refine ⟨19577163471171145742320919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13051442314114097161547279 19577163471171145742320919)
    ·
      refine ⟨29365745206756718613481379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19577163471171145742320919 29365745206756718613481379)
      ·
        refine ⟨44048617810135077920222069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29365745206756718613481379 44048617810135077920222069)
        ·
          refine ⟨4129557919700163555020819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44048617810135077920222069 4129557919700163555020819)
          ·
            refine ⟨6194336879550245332531229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129557919700163555020819 6194336879550245332531229)
            ·
              refine ⟨2322876329831341999699211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6194336879550245332531229 2322876329831341999699211)
              ·
                refine ⟨3484314494747012999548817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322876329831341999699211 3484314494747012999548817)
                ·
                  refine ⟨2613235871060259749661613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484314494747012999548817 2613235871060259749661613)
                  ·
                    refine ⟨979963451647597406123105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613235871060259749661613 979963451647597406123105)
                    ·
                      refine ⟨734972588735698054592329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 979963451647597406123105 734972588735698054592329)
                      ·
                        rfl

theorem cell23_1431354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_1431354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431354 prefixEnd_1431354 := by exact prefixLift 1431354
  have htrace : WordTrace (prefixWord ++ tailWord_1431354) baseStart_1431354 baseEnd_1431354 := by
    simpa [prefixWord, tailWord_1431354, baseEnd_1431354] using wordTrace_append hprefix tailTrace_1431354
  have hstable : (prefixWord ++ tailWord_1431354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431354).length < 2 ^ (prefixWord ++ tailWord_1431354).sum := by decide
  have hdescent : baseEnd_1431354 < baseStart_1431354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431370 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1431370 : Nat := 118140960795 + 1431370 * 2 ^ 59
def prefixEnd_1431370 : Nat := 4983230072969 + 3 ^ 40 * 1431370 * 2
def baseEnd_1431370 : Nat := 734980804426169991992255

theorem tailTrace_1431370 : CollatzResearch.WordTrace tailWord_1431370 prefixEnd_1431370 734980804426169991992255 := by
  unfold tailWord_1431370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051588206099605844692891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34804235216265615585847709 13051588206099605844692891)
  ·
    refine ⟨19577382309149408767039337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13051588206099605844692891 19577382309149408767039337)
    ·
      refine ⟨14683036731862056575279503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19577382309149408767039337 14683036731862056575279503)
      ·
        refine ⟨22024555097793084862919255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14683036731862056575279503 22024555097793084862919255)
        ·
          refine ⟨33036832646689627294378883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22024555097793084862919255 33036832646689627294378883)
          ·
            refine ⟨49555248970034440941568325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33036832646689627294378883 49555248970034440941568325)
            ·
              refine ⟨9291609181881457676544061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49555248970034440941568325 9291609181881457676544061)
              ·
                refine ⟨3484353443205546628704023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9291609181881457676544061 3484353443205546628704023)
                ·
                  refine ⟨5226530164808319943056035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484353443205546628704023 5226530164808319943056035)
                  ·
                    refine ⟨7839795247212479914584053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226530164808319943056035 7839795247212479914584053)
                    ·
                      refine ⟨734980804426169991992255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7839795247212479914584053 734980804426169991992255)
                      ·
                        rfl

theorem cell23_1431370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1431370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431370 prefixEnd_1431370 := by exact prefixLift 1431370
  have htrace : WordTrace (prefixWord ++ tailWord_1431370) baseStart_1431370 baseEnd_1431370 := by
    simpa [prefixWord, tailWord_1431370, baseEnd_1431370] using wordTrace_append hprefix tailTrace_1431370
  have hstable : (prefixWord ++ tailWord_1431370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431370).length < 2 ^ (prefixWord ++ tailWord_1431370).sum := by decide
  have hdescent : baseEnd_1431370 < baseStart_1431370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431377 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_1431377 : Nat := 118140960795 + 1431377 * 2 ^ 59
def prefixEnd_1431377 : Nat := 4983230072969 + 3 ^ 40 * 1431377 * 2
def baseEnd_1431377 : Nat := 244994799596917154868241

theorem tailTrace_1431377 : CollatzResearch.WordTrace tailWord_1431377 prefixEnd_1431377 244994799596917154868241 := by
  unfold tailWord_1431377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52206608135373063574276385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34804405423582042382850923 52206608135373063574276385)
  ·
    refine ⟨39154956101529797680707289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52206608135373063574276385 39154956101529797680707289)
    ·
      refine ⟨29366217076147348260530467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39154956101529797680707289 29366217076147348260530467)
      ·
        refine ⟨44049325614221022390795701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29366217076147348260530467 44049325614221022390795701)
        ·
          refine ⟨4129624276333220849137097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44049325614221022390795701 4129624276333220849137097)
          ·
            refine ⟨3097218207249915636852823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4129624276333220849137097 3097218207249915636852823)
            ·
              refine ⟨4645827310874873455279235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097218207249915636852823 4645827310874873455279235)
              ·
                refine ⟨6968740966312310182918853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645827310874873455279235 6968740966312310182918853)
                ·
                  refine ⟨1306638931183558159297285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6968740966312310182918853 1306638931183558159297285)
                  ·
                    refine ⟨244994799596917154868241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306638931183558159297285 244994799596917154868241)
                    ·
                      rfl

theorem cell23_1431377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_1431377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431377 prefixEnd_1431377 := by exact prefixLift 1431377
  have htrace : WordTrace (prefixWord ++ tailWord_1431377) baseStart_1431377 baseEnd_1431377 := by
    simpa [prefixWord, tailWord_1431377, baseEnd_1431377] using wordTrace_append hprefix tailTrace_1431377
  have hstable : (prefixWord ++ tailWord_1431377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431377).length < 2 ^ (prefixWord ++ tailWord_1431377).sum := by decide
  have hdescent : baseEnd_1431377 < baseStart_1431377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431394 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1431394 : Nat := 118140960795 + 1431394 * 2 ^ 59
def prefixEnd_1431394 : Nat := 4983230072969 + 3 ^ 40 * 1431394 * 2
def baseEnd_1431394 : Nat := 244997709320625966030715

theorem tailTrace_1431394 : CollatzResearch.WordTrace tailWord_1431394 prefixEnd_1431394 244997709320625966030715 := by
  unfold tailWord_1431394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051807044077868869411309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34804818784207650318430157 13051807044077868869411309)
  ·
    refine ⟨4894427641529200826029241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13051807044077868869411309 4894427641529200826029241)
    ·
      refine ⟨3670820731146900619521931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894427641529200826029241 3670820731146900619521931)
      ·
        refine ⟨5506231096720350929282897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670820731146900619521931 5506231096720350929282897)
        ·
          refine ⟨4129673322540263196962173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506231096720350929282897 4129673322540263196962173)
          ·
            refine ⟨1548627495952598698860815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4129673322540263196962173 1548627495952598698860815)
            ·
              refine ⟨2322941243928898048291223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548627495952598698860815 2322941243928898048291223)
              ·
                refine ⟨3484411865893347072436835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322941243928898048291223 3484411865893347072436835)
                ·
                  refine ⟨5226617798840020608655253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484411865893347072436835 5226617798840020608655253)
                  ·
                    refine ⟨244997709320625966030715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5226617798840020608655253 244997709320625966030715)
                    ·
                      rfl

theorem cell23_1431394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1431394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431394 prefixEnd_1431394 := by exact prefixLift 1431394
  have htrace : WordTrace (prefixWord ++ tailWord_1431394) baseStart_1431394 baseEnd_1431394 := by
    simpa [prefixWord, tailWord_1431394, baseEnd_1431394] using wordTrace_append hprefix tailTrace_1431394
  have hstable : (prefixWord ++ tailWord_1431394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431394).length < 2 ^ (prefixWord ++ tailWord_1431394).sum := by decide
  have hdescent : baseEnd_1431394 < baseStart_1431394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431404 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_1431404 : Nat := 118140960795 + 1431404 * 2 ^ 59
def prefixEnd_1431404 : Nat := 4983230072969 + 3 ^ 40 * 1431404 * 2
def baseEnd_1431404 : Nat := 734998262768422858967099

theorem tailTrace_1431404 : CollatzResearch.WordTrace tailWord_1431404 prefixEnd_1431404 734998262768422858967099 := by
  unfold tailWord_1431404
  simp only [CollatzResearch.WordTrace]
  refine ⟨26103796453137623592754633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34805061937516831457006177 26103796453137623592754633)
  ·
    refine ⟨19577847339853217694565975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26103796453137623592754633 19577847339853217694565975)
    ·
      refine ⟨29366771009779826541848963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19577847339853217694565975 29366771009779826541848963)
      ·
        refine ⟨44050156514669739812773445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29366771009779826541848963 44050156514669739812773445)
        ·
          refine ⟨8259404346500576214895021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44050156514669739812773445 8259404346500576214895021)
          ·
            refine ⟨3097276629937716080585633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8259404346500576214895021 3097276629937716080585633)
            ·
              refine ⟨2322957472453287060439225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097276629937716080585633 2322957472453287060439225)
              ·
                refine ⟨1742218104339965295329419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322957472453287060439225 1742218104339965295329419)
                ·
                  refine ⟨2613327156509947942994129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742218104339965295329419 2613327156509947942994129)
                  ·
                    refine ⟨1959995367382460957245597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613327156509947942994129 1959995367382460957245597)
                    ·
                      refine ⟨734998262768422858967099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1959995367382460957245597 734998262768422858967099)
                      ·
                        rfl

theorem cell23_1431404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_1431404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431404 prefixEnd_1431404 := by exact prefixLift 1431404
  have htrace : WordTrace (prefixWord ++ tailWord_1431404) baseStart_1431404 baseEnd_1431404 := by
    simpa [prefixWord, tailWord_1431404, baseEnd_1431404] using wordTrace_append hprefix tailTrace_1431404
  have hstable : (prefixWord ++ tailWord_1431404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431404).length < 2 ^ (prefixWord ++ tailWord_1431404).sum := by decide
  have hdescent : baseEnd_1431404 < baseStart_1431404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431417 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1431417 : Nat := 118140960795 + 1431417 * 2 ^ 59
def prefixEnd_1431417 : Nat := 4983230072969 + 3 ^ 40 * 1431417 * 2
def baseEnd_1431417 : Nat := 735004938016931308104539

theorem tailTrace_1431417 : CollatzResearch.WordTrace tailWord_1431417 prefixEnd_1431417 735004938016931308104539 := by
  unfold tailWord_1431417
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208067055228150405732505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34805378036818766937155003 52208067055228150405732505)
  ·
    refine ⟨39156050291421112804299379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52208067055228150405732505 39156050291421112804299379)
    ·
      refine ⟨58734075437131669206449069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39156050291421112804299379 58734075437131669206449069)
      ·
        refine ⟨22025278288924375952418401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58734075437131669206449069 22025278288924375952418401)
        ·
          refine ⟨16518958716693281964313801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22025278288924375952418401 16518958716693281964313801)
          ·
            refine ⟨12389219037519961473235351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16518958716693281964313801 12389219037519961473235351)
            ·
              refine ⟨18583828556279942209853027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12389219037519961473235351 18583828556279942209853027)
              ·
                refine ⟨27875742834419913314779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18583828556279942209853027 27875742834419913314779541)
                ·
                  refine ⟨1306675445363433436630291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27875742834419913314779541 1306675445363433436630291)
                  ·
                    refine ⟨1960013168045150154945437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1306675445363433436630291 1960013168045150154945437)
                    ·
                      refine ⟨735004938016931308104539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1960013168045150154945437 735004938016931308104539)
                      ·
                        rfl

theorem cell23_1431417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1431417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431417 prefixEnd_1431417 := by exact prefixLift 1431417
  have htrace : WordTrace (prefixWord ++ tailWord_1431417) baseStart_1431417 baseEnd_1431417 := by
    simpa [prefixWord, tailWord_1431417, baseEnd_1431417] using wordTrace_append hprefix tailTrace_1431417
  have hstable : (prefixWord ++ tailWord_1431417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431417).length < 2 ^ (prefixWord ++ tailWord_1431417).sum := by decide
  have hdescent : baseEnd_1431417 < baseStart_1431417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431474 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_1431474 : Nat := 118140960795 + 1431474 * 2 ^ 59
def prefixEnd_1431474 : Nat := 4983230072969 + 3 ^ 40 * 1431474 * 2
def baseEnd_1431474 : Nat := 735034206414237585091777

theorem tailTrace_1431474 : CollatzResearch.WordTrace tailWord_1431474 prefixEnd_1431474 735034206414237585091777 := by
  unfold tailWord_1431474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052536504005412285139369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34806764010681099427038317 13052536504005412285139369)
  ·
    refine ⟨9789402378004059213854527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13052536504005412285139369 9789402378004059213854527)
    ·
      refine ⟨14684103567006088820781791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789402378004059213854527 14684103567006088820781791)
      ·
        refine ⟨22026155350509133231172687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684103567006088820781791 22026155350509133231172687)
        ·
          refine ⟨33039233025763699846759031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22026155350509133231172687 33039233025763699846759031)
          ·
            refine ⟨49558849538645549770138547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33039233025763699846759031 49558849538645549770138547)
            ·
              refine ⟨74338274307968324655207821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49558849538645549770138547 74338274307968324655207821)
              ·
                refine ⟨27876852865488121745702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74338274307968324655207821 27876852865488121745702933)
                ·
                  refine ⟨1306727478069755706829825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27876852865488121745702933 1306727478069755706829825)
                  ·
                    refine ⟨980045608552316780122369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306727478069755706829825 980045608552316780122369)
                    ·
                      refine ⟨735034206414237585091777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980045608552316780122369 735034206414237585091777)
                      ·
                        rfl

theorem cell23_1431474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_1431474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431474 prefixEnd_1431474 := by exact prefixLift 1431474
  have htrace : WordTrace (prefixWord ++ tailWord_1431474) baseStart_1431474 baseEnd_1431474 := by
    simpa [prefixWord, tailWord_1431474, baseEnd_1431474] using wordTrace_append hprefix tailTrace_1431474
  have hstable : (prefixWord ++ tailWord_1431474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431474).length < 2 ^ (prefixWord ++ tailWord_1431474).sum := by decide
  have hdescent : baseEnd_1431474 < baseStart_1431474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431477 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1431477 : Nat := 118140960795 + 1431477 * 2 ^ 59
def prefixEnd_1431477 : Nat := 4983230072969 + 3 ^ 40 * 1431477 * 2
def baseEnd_1431477 : Nat := 735035746856201073354263

theorem tailTrace_1431477 : CollatzResearch.WordTrace tailWord_1431477 prefixEnd_1431477 735035746856201073354263 := by
  unfold tailWord_1431477
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210255435010780652916685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34806836956673853768611123 52210255435010780652916685)
  ·
    refine ⟨19578845788129042744843757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52210255435010780652916685 19578845788129042744843757)
    ·
      refine ⟨7342067170548391029316409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19578845788129042744843757 7342067170548391029316409)
      ·
        refine ⟨5506550377911293271987307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7342067170548391029316409 5506550377911293271987307)
        ·
          refine ⟨8259825566866939907980961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506550377911293271987307 8259825566866939907980961)
          ·
            refine ⟨6194869175150204930985721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259825566866939907980961 6194869175150204930985721)
            ·
              refine ⟨4646151881362653698239291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194869175150204930985721 4646151881362653698239291)
              ·
                refine ⟨6969227822043980547358937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646151881362653698239291 6969227822043980547358937)
                ·
                  refine ⟨5226920866532985410519203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969227822043980547358937 5226920866532985410519203)
                  ·
                    refine ⟨7840381299799478115778805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226920866532985410519203 7840381299799478115778805)
                    ·
                      refine ⟨735035746856201073354263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7840381299799478115778805 735035746856201073354263)
                      ·
                        rfl

theorem cell23_1431477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1431477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431477 prefixEnd_1431477 := by exact prefixLift 1431477
  have htrace : WordTrace (prefixWord ++ tailWord_1431477) baseStart_1431477 baseEnd_1431477 := by
    simpa [prefixWord, tailWord_1431477, baseEnd_1431477] using wordTrace_append hprefix tailTrace_1431477
  have hstable : (prefixWord ++ tailWord_1431477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431477).length < 2 ^ (prefixWord ++ tailWord_1431477).sum := by decide
  have hdescent : baseEnd_1431477 < baseStart_1431477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431497 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 5]
def baseStart_1431497 : Nat := 118140960795 + 1431497 * 2 ^ 59
def prefixEnd_1431497 : Nat := 4983230072969 + 3 ^ 40 * 1431497 * 2
def baseEnd_1431497 : Nat := 81671779607698999456019

theorem tailTrace_1431497 : CollatzResearch.WordTrace tailWord_1431497 prefixEnd_1431497 81671779607698999456019 := by
  unfold tailWord_1431497
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210984894938324068644745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34807323263292216045763163 52210984894938324068644745)
  ·
    refine ⟨39158238671203743051483559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52210984894938324068644745 39158238671203743051483559)
    ·
      refine ⟨58737358006805614577225339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39158238671203743051483559 58737358006805614577225339)
      ·
        refine ⟨88106037010208421865838009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58737358006805614577225339 88106037010208421865838009)
        ·
          refine ⟨66079527757656316399378507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88106037010208421865838009 66079527757656316399378507)
          ·
            refine ⟨99119291636484474599067761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66079527757656316399378507 99119291636484474599067761)
            ·
              refine ⟨74339468727363355949300821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99119291636484474599067761 74339468727363355949300821)
              ·
                refine ⟨871165649148789327530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74339468727363355949300821 871165649148789327530869)
                ·
                  refine ⟨81671779607698999456019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871165649148789327530869 81671779607698999456019)
                  ·
                    rfl

theorem cell23_1431497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 5].length) (baseStart_1431497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431497 prefixEnd_1431497 := by exact prefixLift 1431497
  have htrace : WordTrace (prefixWord ++ tailWord_1431497) baseStart_1431497 baseEnd_1431497 := by
    simpa [prefixWord, tailWord_1431497, baseEnd_1431497] using wordTrace_append hprefix tailTrace_1431497
  have hstable : (prefixWord ++ tailWord_1431497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431497).length < 2 ^ (prefixWord ++ tailWord_1431497).sum := by decide
  have hdescent : baseEnd_1431497 < baseStart_1431497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431520 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1431520 : Nat := 118140960795 + 1431520 * 2 ^ 59
def prefixEnd_1431520 : Nat := 4983230072969 + 3 ^ 40 * 1431520 * 2
def baseEnd_1431520 : Nat := 735057826524344405116565

theorem tailTrace_1431520 : CollatzResearch.WordTrace tailWord_1431520 prefixEnd_1431520 735057826524344405116565 := by
  unfold tailWord_1431520
  simp only [CollatzResearch.WordTrace]
  refine ⟨26105911886927499498366007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34807882515903332664488009 26105911886927499498366007)
  ·
    refine ⟨39158867830391249247549011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26105911886927499498366007 39158867830391249247549011)
    ·
      refine ⟨58738301745586873871323517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39158867830391249247549011 58738301745586873871323517)
      ·
        refine ⟨22026863154595077701746319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58738301745586873871323517 22026863154595077701746319)
        ·
          refine ⟨33040294731892616552619479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22026863154595077701746319 33040294731892616552619479)
          ·
            refine ⟨49560442097838924828929219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33040294731892616552619479 49560442097838924828929219)
            ·
              refine ⟨74340663146758387243393829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49560442097838924828929219 74340663146758387243393829)
              ·
                refine ⟨13938874340017197608136343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74340663146758387243393829 13938874340017197608136343)
                ·
                  refine ⟨20908311510025796412204515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13938874340017197608136343 20908311510025796412204515)
                  ·
                    refine ⟨31362467265038694618306773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20908311510025796412204515 31362467265038694618306773)
                    ·
                      refine ⟨735057826524344405116565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31362467265038694618306773 735057826524344405116565)
                      ·
                        rfl

theorem cell23_1431520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1431520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431520 prefixEnd_1431520 := by exact prefixLift 1431520
  have htrace : WordTrace (prefixWord ++ tailWord_1431520) baseStart_1431520 baseEnd_1431520 := by
    simpa [prefixWord, tailWord_1431520, baseEnd_1431520] using wordTrace_append hprefix tailTrace_1431520
  have hstable : (prefixWord ++ tailWord_1431520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431520).length < 2 ^ (prefixWord ++ tailWord_1431520).sum := by decide
  have hdescent : baseEnd_1431520 < baseStart_1431520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431542 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1431542 : Nat := 118140960795 + 1431542 * 2 ^ 59
def prefixEnd_1431542 : Nat := 4983230072969 + 3 ^ 40 * 1431542 * 2
def baseEnd_1431542 : Nat := 735069123098743319041465

theorem tailTrace_1431542 : CollatzResearch.WordTrace tailWord_1431542 prefixEnd_1431542 735069123098743319041465 := by
  unfold tailWord_1431542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263289136235956047127055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34808417453183531169355253 3263289136235956047127055)
  ·
    refine ⟨4894933704353934070690583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263289136235956047127055 4894933704353934070690583)
    ·
      refine ⟨7342400556530901106035875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894933704353934070690583 7342400556530901106035875)
      ·
        refine ⟨11013600834796351659053813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342400556530901106035875 11013600834796351659053813)
        ·
          refine ⟨1032525078262157968036295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11013600834796351659053813 1032525078262157968036295)
          ·
            refine ⟨1548787617393236952054443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032525078262157968036295 1548787617393236952054443)
            ·
              refine ⟨2323181426089855428081665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548787617393236952054443 2323181426089855428081665)
              ·
                refine ⟨1742386069567391571061249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323181426089855428081665 1742386069567391571061249)
                ·
                  refine ⟨1306789552175543678295937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742386069567391571061249 1306789552175543678295937)
                  ·
                    refine ⟨980092164131657758721953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306789552175543678295937 980092164131657758721953)
                    ·
                      refine ⟨735069123098743319041465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980092164131657758721953 735069123098743319041465)
                      ·
                        rfl

theorem cell23_1431542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1431542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431542 prefixEnd_1431542 := by exact prefixLift 1431542
  have htrace : WordTrace (prefixWord ++ tailWord_1431542) baseStart_1431542 baseEnd_1431542 := by
    simpa [prefixWord, tailWord_1431542, baseEnd_1431542] using wordTrace_append hprefix tailTrace_1431542
  have hstable : (prefixWord ++ tailWord_1431542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431542).length < 2 ^ (prefixWord ++ tailWord_1431542).sum := by decide
  have hdescent : baseEnd_1431542 < baseStart_1431542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431547 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4]
def baseStart_1431547 : Nat := 118140960795 + 1431547 * 2 ^ 59
def prefixEnd_1431547 : Nat := 4983230072969 + 3 ^ 40 * 1431547 * 2
def baseEnd_1431547 : Nat := 735071690502015799478941

theorem tailTrace_1431547 : CollatzResearch.WordTrace tailWord_1431547 prefixEnd_1431547 735071690502015799478941 := by
  unfold tailWord_1431547
  simp only [CollatzResearch.WordTrace]
  refine ⟨52212808544757182607964895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34808539029838121738643263 52212808544757182607964895)
  ·
    refine ⟨78319212817135773911947343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52212808544757182607964895 78319212817135773911947343)
    ·
      refine ⟨117478819225703660867921015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78319212817135773911947343 117478819225703660867921015)
      ·
        refine ⟨176218228838555491301881523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117478819225703660867921015 176218228838555491301881523)
        ·
          refine ⟨264327343257833236952822285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176218228838555491301881523 264327343257833236952822285)
          ·
            refine ⟨99122753721687463857308357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264327343257833236952822285 99122753721687463857308357)
            ·
              refine ⟨18585516322816399473245317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99122753721687463857308357 18585516322816399473245317)
              ·
                refine ⟨3484784310528074901233497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18585516322816399473245317 3484784310528074901233497)
                ·
                  refine ⟨2613588232896056175925123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484784310528074901233497 2613588232896056175925123)
                  ·
                    refine ⟨3920382349344084263887685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613588232896056175925123 3920382349344084263887685)
                    ·
                      refine ⟨735071690502015799478941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3920382349344084263887685 735071690502015799478941)
                      ·
                        rfl

theorem cell23_1431547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_1431547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431547 prefixEnd_1431547 := by exact prefixLift 1431547
  have htrace : WordTrace (prefixWord ++ tailWord_1431547) baseStart_1431547 baseEnd_1431547 := by
    simpa [prefixWord, tailWord_1431547, baseEnd_1431547] using wordTrace_append hprefix tailTrace_1431547
  have hstable : (prefixWord ++ tailWord_1431547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431547).length < 2 ^ (prefixWord ++ tailWord_1431547).sum := by decide
  have hdescent : baseEnd_1431547 < baseStart_1431547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431564 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_1431564 : Nat := 118140960795 + 1431564 * 2 ^ 59
def prefixEnd_1431564 : Nat := 4983230072969 + 3 ^ 40 * 1431564 * 2
def baseEnd_1431564 : Nat := 735080419673142232966363

theorem tailTrace_1431564 : CollatzResearch.WordTrace tailWord_1431564 prefixEnd_1431564 735080419673142232966363 := by
  unfold tailWord_1431564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26106714292847797255666873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34808952390463729674222497 26106714292847797255666873)
  ·
    refine ⟨19580035719635847941750155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26106714292847797255666873 19580035719635847941750155)
    ·
      refine ⟨29370053579453771912625233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19580035719635847941750155 29370053579453771912625233)
      ·
        refine ⟨22027540184590328934468925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29370053579453771912625233 22027540184590328934468925)
        ·
          refine ⟨8260327569221373350425847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22027540184590328934468925 8260327569221373350425847)
          ·
            refine ⟨12390491353832060025638771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260327569221373350425847 12390491353832060025638771)
            ·
              refine ⟨18585737030748090038458157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12390491353832060025638771 18585737030748090038458157)
              ·
                refine ⟨6969651386530533764421809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18585737030748090038458157 6969651386530533764421809)
                ·
                  refine ⟨5227238539897900323316357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969651386530533764421809 5227238539897900323316357)
                  ·
                    refine ⟨980107226230856310621817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227238539897900323316357 980107226230856310621817)
                    ·
                      refine ⟨735080419673142232966363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980107226230856310621817 735080419673142232966363)
                      ·
                        rfl

theorem cell23_1431564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_1431564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431564 prefixEnd_1431564 := by exact prefixLift 1431564
  have htrace : WordTrace (prefixWord ++ tailWord_1431564) baseStart_1431564 baseEnd_1431564 := by
    simpa [prefixWord, tailWord_1431564, baseEnd_1431564] using wordTrace_append hprefix tailTrace_1431564
  have hstable : (prefixWord ++ tailWord_1431564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431564).length < 2 ^ (prefixWord ++ tailWord_1431564).sum := by decide
  have hdescent : baseEnd_1431564 < baseStart_1431564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431608 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_1431608 : Nat := 118140960795 + 1431608 * 2 ^ 59
def prefixEnd_1431608 : Nat := 4983230072969 + 3 ^ 40 * 1431608 * 2
def baseEnd_1431608 : Nat := 245034337607313353605387

theorem tailTrace_1431608 : CollatzResearch.WordTrace tailWord_1431608 prefixEnd_1431608 245034337607313353605387 := by
  unfold tailWord_1431608
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107516698768095012967739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34810022265024126683956985 26107516698768095012967739)
  ·
    refine ⟨39161275048152142519451609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26107516698768095012967739 39161275048152142519451609)
    ·
      refine ⟨29370956286114106889588707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39161275048152142519451609 29370956286114106889588707)
      ·
        refine ⟨44056434429171160334383061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29370956286114106889588707 44056434429171160334383061)
        ·
          refine ⟨1032572681933699070337103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44056434429171160334383061 1032572681933699070337103)
          ·
            refine ⟨1548859022900548605505655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032572681933699070337103 1548859022900548605505655)
            ·
              refine ⟨2323288534350822908258483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548859022900548605505655 2323288534350822908258483)
              ·
                refine ⟨3484932801526234362387725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323288534350822908258483 3484932801526234362387725)
                ·
                  refine ⟨1306849800572337885895397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3484932801526234362387725 1306849800572337885895397)
                  ·
                    refine ⟨245034337607313353605387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306849800572337885895397 245034337607313353605387)
                    ·
                      rfl

theorem cell23_1431608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_1431608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431608 prefixEnd_1431608 := by exact prefixLift 1431608
  have htrace : WordTrace (prefixWord ++ tailWord_1431608) baseStart_1431608 baseEnd_1431608 := by
    simpa [prefixWord, tailWord_1431608, baseEnd_1431608] using wordTrace_append hprefix tailTrace_1431608
  have hstable : (prefixWord ++ tailWord_1431608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431608).length < 2 ^ (prefixWord ++ tailWord_1431608).sum := by decide
  have hdescent : baseEnd_1431608 < baseStart_1431608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431624 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_1431624 : Nat := 118140960795 + 1431624 * 2 ^ 59
def prefixEnd_1431624 : Nat := 4983230072969 + 3 ^ 40 * 1431624 * 2
def baseEnd_1431624 : Nat := 735111228512411998216087

theorem tailTrace_1431624 : CollatzResearch.WordTrace tailWord_1431624 prefixEnd_1431624 735111228512411998216087 := by
  unfold tailWord_1431624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107808482739112379258963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34810411310318816505678617 26107808482739112379258963)
  ·
    refine ⟨39161712724108668568888445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26107808482739112379258963 39161712724108668568888445)
    ·
      refine ⟨14685642271540750713333167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39161712724108668568888445 14685642271540750713333167)
      ·
        refine ⟨22028463407311126069999751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14685642271540750713333167 22028463407311126069999751)
        ·
          refine ⟨33042695110966689104999627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22028463407311126069999751 33042695110966689104999627)
          ·
            refine ⟨49564042666450033657499441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33042695110966689104999627 49564042666450033657499441)
            ·
              refine ⟨37173031999837525243124581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49564042666450033657499441 37173031999837525243124581)
              ·
                refine ⟨6969943499969535983085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37173031999837525243124581 6969943499969535983085859)
                ·
                  refine ⟨10454915249954303974628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969943499969535983085859 10454915249954303974628789)
                  ·
                    refine ⟨980148304683215997621449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454915249954303974628789 980148304683215997621449)
                    ·
                      refine ⟨735111228512411998216087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980148304683215997621449 735111228512411998216087)
                      ·
                        rfl

theorem cell23_1431624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_1431624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431624 prefixEnd_1431624 := by exact prefixLift 1431624
  have htrace : WordTrace (prefixWord ++ tailWord_1431624) baseStart_1431624 baseEnd_1431624 := by
    simpa [prefixWord, tailWord_1431624, baseEnd_1431624] using wordTrace_append hprefix tailTrace_1431624
  have hstable : (prefixWord ++ tailWord_1431624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431624).length < 2 ^ (prefixWord ++ tailWord_1431624).sum := by decide
  have hdescent : baseEnd_1431624 < baseStart_1431624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431641 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 2, 3, 2]
def baseStart_1431641 : Nat := 118140960795 + 1431641 * 2 ^ 59
def prefixEnd_1431641 : Nat := 4983230072969 + 3 ^ 40 * 1431641 * 2
def baseEnd_1431641 : Nat := 735119957683538431703509

theorem tailTrace_1431641 : CollatzResearch.WordTrace tailWord_1431641 prefixEnd_1431641 735119957683538431703509 := by
  unfold tailWord_1431641
  simp only [CollatzResearch.WordTrace]
  refine ⟨52216237006416636661886777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34810824670944424441257851 52216237006416636661886777)
  ·
    refine ⟨39162177754812477496415083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52216237006416636661886777 39162177754812477496415083)
    ·
      refine ⟨58743266632218716244622625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39162177754812477496415083 58743266632218716244622625)
      ·
        refine ⟨44057449974164037183466969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58743266632218716244622625 44057449974164037183466969)
        ·
          refine ⟨33043087480623027887600227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44057449974164037183466969 33043087480623027887600227)
          ·
            refine ⟨49564631220934541831400341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33043087480623027887600227 49564631220934541831400341)
            ·
              refine ⟨2323342088481306648346891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49564631220934541831400341 2323342088481306648346891)
              ·
                refine ⟨3485013132721959972520337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323342088481306648346891 3485013132721959972520337)
                ·
                  refine ⟨2613759849541469979390253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3485013132721959972520337 2613759849541469979390253)
                  ·
                    refine ⟨980159943578051242271345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613759849541469979390253 980159943578051242271345)
                    ·
                      refine ⟨735119957683538431703509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980159943578051242271345 735119957683538431703509)
                      ·
                        rfl

theorem cell23_1431641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_1431641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431641 prefixEnd_1431641 := by exact prefixLift 1431641
  have htrace : WordTrace (prefixWord ++ tailWord_1431641) baseStart_1431641 baseEnd_1431641 := by
    simpa [prefixWord, tailWord_1431641, baseEnd_1431641] using wordTrace_append hprefix tailTrace_1431641
  have hstable : (prefixWord ++ tailWord_1431641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431641).length < 2 ^ (prefixWord ++ tailWord_1431641).sum := by decide
  have hdescent : baseEnd_1431641 < baseStart_1431641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431681 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1431681 : Nat := 118140960795 + 1431681 * 2 ^ 59
def prefixEnd_1431681 : Nat := 4983230072969 + 3 ^ 40 * 1431681 * 2
def baseEnd_1431681 : Nat := 245046832303239425067775

theorem tailTrace_1431681 : CollatzResearch.WordTrace tailWord_1431681 prefixEnd_1431681 245046832303239425067775 := by
  unfold tailWord_1431681
  simp only [CollatzResearch.WordTrace]
  refine ⟨52217695926271723493342897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34811797284181148995561931 52217695926271723493342897)
  ·
    refine ⟨39163271944703792620007173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52217695926271723493342897 39163271944703792620007173)
    ·
      refine ⟨7343113489631961116251345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39163271944703792620007173 7343113489631961116251345)
      ·
        refine ⟨5507335117223970837188509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7343113489631961116251345 5507335117223970837188509)
        ·
          refine ⟨2065250668958989063945691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5507335117223970837188509 2065250668958989063945691)
          ·
            refine ⟨3097876003438483595918537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065250668958989063945691 3097876003438483595918537)
            ·
              refine ⟨2323407002578862696938903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097876003438483595918537 2323407002578862696938903)
              ·
                refine ⟨3485110503868294045408355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323407002578862696938903 3485110503868294045408355)
                ·
                  refine ⟨5227665755802441068112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485110503868294045408355 5227665755802441068112533)
                  ·
                    refine ⟨245046832303239425067775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5227665755802441068112533 245046832303239425067775)
                    ·
                      rfl

theorem cell23_1431681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1431681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431681 prefixEnd_1431681 := by exact prefixLift 1431681
  have htrace : WordTrace (prefixWord ++ tailWord_1431681) baseStart_1431681 baseEnd_1431681 := by
    simpa [prefixWord, tailWord_1431681, baseEnd_1431681] using wordTrace_append hprefix tailTrace_1431681
  have hstable : (prefixWord ++ tailWord_1431681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431681).length < 2 ^ (prefixWord ++ tailWord_1431681).sum := by decide
  have hdescent : baseEnd_1431681 < baseStart_1431681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431688 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1431688 : Nat := 118140960795 + 1431688 * 2 ^ 59
def prefixEnd_1431688 : Nat := 4983230072969 + 3 ^ 40 * 1431688 * 2
def baseEnd_1431688 : Nat := 735144091274299747815793

theorem tailTrace_1431688 : CollatzResearch.WordTrace tailWord_1431688 prefixEnd_1431688 735144091274299747815793 := by
  unfold tailWord_1431688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26108975618623181844423859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34811967491497575792565145 26108975618623181844423859)
  ·
    refine ⟨39163463427934772766635789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26108975618623181844423859 39163463427934772766635789)
    ·
      refine ⟨14686298785475539787488421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39163463427934772766635789 14686298785475539787488421)
      ·
        refine ⟨2753681022276663710154079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14686298785475539787488421 2753681022276663710154079)
        ·
          refine ⟨4130521533414995565231119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753681022276663710154079 4130521533414995565231119)
          ·
            refine ⟨6195782300122493347846679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130521533414995565231119 6195782300122493347846679)
            ·
              refine ⟨9293673450183740021770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195782300122493347846679 9293673450183740021770019)
              ·
                refine ⟨13940510175275610032655029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9293673450183740021770019 13940510175275610032655029)
                ·
                  refine ⟨1306922828932088440561409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13940510175275610032655029 1306922828932088440561409)
                  ·
                    refine ⟨980192121699066330421057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306922828932088440561409 980192121699066330421057)
                    ·
                      refine ⟨735144091274299747815793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980192121699066330421057 735144091274299747815793)
                      ·
                        rfl

theorem cell23_1431688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1431688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431688 prefixEnd_1431688 := by exact prefixLift 1431688
  have htrace : WordTrace (prefixWord ++ tailWord_1431688) baseStart_1431688 baseEnd_1431688 := by
    simpa [prefixWord, tailWord_1431688, baseEnd_1431688] using wordTrace_append hprefix tailTrace_1431688
  have hstable : (prefixWord ++ tailWord_1431688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431688).length < 2 ^ (prefixWord ++ tailWord_1431688).sum := by decide
  have hdescent : baseEnd_1431688 < baseStart_1431688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431722 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1431722 : Nat := 118140960795 + 1431722 * 2 ^ 59
def prefixEnd_1431722 : Nat := 4983230072969 + 3 ^ 40 * 1431722 * 2
def baseEnd_1431722 : Nat := 735161549616552614790637

theorem tailTrace_1431722 : CollatzResearch.WordTrace tailWord_1431722 prefixEnd_1431722 735161549616552614790637 := by
  unfold tailWord_1431722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13054797829780796873896355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34812794212748791663723613 13054797829780796873896355)
  ·
    refine ⟨19582196744671195310844533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13054797829780796873896355 19582196744671195310844533)
    ·
      refine ⟨1835830944812924560391675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19582196744671195310844533 1835830944812924560391675)
      ·
        refine ⟨2753746417219386840587513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835830944812924560391675 2753746417219386840587513)
        ·
          refine ⟨2065309812914540130440635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753746417219386840587513 2065309812914540130440635)
          ·
            refine ⟨3097964719371810195660953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065309812914540130440635 3097964719371810195660953)
            ·
              refine ⟨2323473539528857646745715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097964719371810195660953 2323473539528857646745715)
              ·
                refine ⟨3485210309293286470118573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323473539528857646745715 3485210309293286470118573)
                ·
                  refine ⟨1306953865984982426294465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3485210309293286470118573 1306953865984982426294465)
                  ·
                    refine ⟨980215399488736819720849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306953865984982426294465 980215399488736819720849)
                    ·
                      refine ⟨735161549616552614790637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980215399488736819720849 735161549616552614790637)
                      ·
                        rfl

theorem cell23_1431722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1431722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431722 prefixEnd_1431722 := by exact prefixLift 1431722
  have htrace : WordTrace (prefixWord ++ tailWord_1431722) baseStart_1431722 baseEnd_1431722 := by
    simpa [prefixWord, tailWord_1431722, baseEnd_1431722] using wordTrace_append hprefix tailTrace_1431722
  have hstable : (prefixWord ++ tailWord_1431722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431722).length < 2 ^ (prefixWord ++ tailWord_1431722).sum := by decide
  have hdescent : baseEnd_1431722 < baseStart_1431722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431732 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1431732 : Nat := 118140960795 + 1431732 * 2 ^ 59
def prefixEnd_1431732 : Nat := 4983230072969 + 3 ^ 40 * 1431732 * 2
def baseEnd_1431732 : Nat := 245055561474365858555197

theorem tailTrace_1431732 : CollatzResearch.WordTrace tailWord_1431732 prefixEnd_1431732 245055561474365858555197 := by
  unfold tailWord_1431732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26109778024543479601724725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34813037366057972802299633 26109778024543479601724725)
  ·
    refine ⟨2447791689800951212661693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26109778024543479601724725 2447791689800951212661693)
    ·
      refine ⟨917921883675356704748135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2447791689800951212661693 917921883675356704748135)
      ·
        refine ⟨1376882825513035057122203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917921883675356704748135 1376882825513035057122203)
        ·
          refine ⟨2065324238269552585683305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376882825513035057122203 2065324238269552585683305)
          ·
            refine ⟨1548993178702164439262479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2065324238269552585683305 1548993178702164439262479)
            ·
              refine ⟨2323489768053246658893719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548993178702164439262479 2323489768053246658893719)
              ·
                refine ⟨3485234652079869988340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323489768053246658893719 3485234652079869988340579)
                ·
                  refine ⟨5227851978119804982510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485234652079869988340579 5227851978119804982510869)
                  ·
                    refine ⟨245055561474365858555197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5227851978119804982510869 245055561474365858555197)
                    ·
                      rfl

theorem cell23_1431732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1431732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431732 prefixEnd_1431732 := by exact prefixLift 1431732
  have htrace : WordTrace (prefixWord ++ tailWord_1431732) baseStart_1431732 baseEnd_1431732 := by
    simpa [prefixWord, tailWord_1431732, baseEnd_1431732] using wordTrace_append hprefix tailTrace_1431732
  have hstable : (prefixWord ++ tailWord_1431732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431732).length < 2 ^ (prefixWord ++ tailWord_1431732).sum := by decide
  have hdescent : baseEnd_1431732 < baseStart_1431732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431745 : List Nat := [1, 2, 6, 1, 3, 1, 2, 7]
def baseStart_1431745 : Nat := 118140960795 + 1431745 * 2 ^ 59
def prefixEnd_1431745 : Nat := 4983230072969 + 3 ^ 40 * 1431745 * 2
def baseEnd_1431745 : Nat := 27228642950800223140853

theorem tailTrace_1431745 : CollatzResearch.WordTrace tailWord_1431745 prefixEnd_1431745 27228642950800223140853 := by
  unfold tailWord_1431745
  simp only [CollatzResearch.WordTrace]
  refine ⟨52220030198039862423672689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34813353465359908282448459 52220030198039862423672689)
  ·
    refine ⟨39165022648529896817754517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52220030198039862423672689 39165022648529896817754517)
    ·
      refine ⟨1835860436649838913332243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39165022648529896817754517 1835860436649838913332243)
      ·
        refine ⟨2753790654974758369998365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835860436649838913332243 2753790654974758369998365)
        ·
          refine ⟨1032671495615534388749387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2753790654974758369998365 1032671495615534388749387)
          ·
            refine ⟨1549007243423301583124081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032671495615534388749387 1549007243423301583124081)
            ·
              refine ⟨1161755432567476187343061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549007243423301583124081 1161755432567476187343061)
              ·
                refine ⟨27228642950800223140853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1161755432567476187343061 27228642950800223140853)
                ·
                  rfl

theorem cell23_1431745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 7].length) (baseStart_1431745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431745 prefixEnd_1431745 := by exact prefixLift 1431745
  have htrace : WordTrace (prefixWord ++ tailWord_1431745) baseStart_1431745 baseEnd_1431745 := by
    simpa [prefixWord, tailWord_1431745, baseEnd_1431745] using wordTrace_append hprefix tailTrace_1431745
  have hstable : (prefixWord ++ tailWord_1431745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431745).length < 2 ^ (prefixWord ++ tailWord_1431745).sum := by decide
  have hdescent : baseEnd_1431745 < baseStart_1431745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431756 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1431756 : Nat := 118140960795 + 1431756 * 2 ^ 59
def prefixEnd_1431756 : Nat := 4983230072969 + 3 ^ 40 * 1431756 * 2
def baseEnd_1431756 : Nat := 735179007958805481765481

theorem tailTrace_1431756 : CollatzResearch.WordTrace tailWord_1431756 prefixEnd_1431756 735179007958805481765481 := by
  unfold tailWord_1431756
  simp only [CollatzResearch.WordTrace]
  refine ⟨26110215700500005651161561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34813620934000007534882081 26110215700500005651161561)
  ·
    refine ⟨19582661775375004238371171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26110215700500005651161561 19582661775375004238371171)
    ·
      refine ⟨29373992663062506357556757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582661775375004238371171 29373992663062506357556757)
      ·
        refine ⟨1376905906081054985510473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29373992663062506357556757 1376905906081054985510473)
        ·
          refine ⟨1032679429560791239132855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376905906081054985510473 1032679429560791239132855)
          ·
            refine ⟨1549019144341186858699283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032679429560791239132855 1549019144341186858699283)
            ·
              refine ⟨2323528716511780288048925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549019144341186858699283 2323528716511780288048925)
              ·
                refine ⟨871323268691917608018347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323528716511780288048925 871323268691917608018347)
                ·
                  refine ⟨1306984903037876412027521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871323268691917608018347 1306984903037876412027521)
                  ·
                    refine ⟨980238677278407309020641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306984903037876412027521 980238677278407309020641)
                    ·
                      refine ⟨735179007958805481765481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980238677278407309020641 735179007958805481765481)
                      ·
                        rfl

theorem cell23_1431756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1431756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431756 prefixEnd_1431756 := by exact prefixLift 1431756
  have htrace : WordTrace (prefixWord ++ tailWord_1431756) baseStart_1431756 baseEnd_1431756 := by
    simpa [prefixWord, tailWord_1431756, baseEnd_1431756] using wordTrace_append hprefix tailTrace_1431756
  have hstable : (prefixWord ++ tailWord_1431756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431756).length < 2 ^ (prefixWord ++ tailWord_1431756).sum := by decide
  have hdescent : baseEnd_1431756 < baseStart_1431756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431761 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_1431761 : Nat := 118140960795 + 1431761 * 2 ^ 59
def prefixEnd_1431761 : Nat := 4983230072969 + 3 ^ 40 * 1431761 * 2
def baseEnd_1431761 : Nat := 735181575362077962202957

theorem tailTrace_1431761 : CollatzResearch.WordTrace tailWord_1431761 prefixEnd_1431761 735181575362077962202957 := by
  unfold tailWord_1431761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52220613765981897156255137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34813742510654598104170091 52220613765981897156255137)
  ·
    refine ⟨39165460324486422867191353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52220613765981897156255137 39165460324486422867191353)
    ·
      refine ⟨29374095243364817150393515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39165460324486422867191353 29374095243364817150393515)
      ·
        refine ⟨44061142865047225725590273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29374095243364817150393515 44061142865047225725590273)
        ·
          refine ⟨33045857148785419294192705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44061142865047225725590273 33045857148785419294192705)
          ·
            refine ⟨24784392861589064470644529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33045857148785419294192705 24784392861589064470644529)
            ·
              refine ⟨18588294646191798352983397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24784392861589064470644529 18588294646191798352983397)
              ·
                refine ⟨3485305246160962191184387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18588294646191798352983397 3485305246160962191184387)
                ·
                  refine ⟨5227957869241443286776581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485305246160962191184387 5227957869241443286776581)
                  ·
                    refine ⟨980242100482770616270609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227957869241443286776581 980242100482770616270609)
                    ·
                      refine ⟨735181575362077962202957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980242100482770616270609 735181575362077962202957)
                      ·
                        rfl

theorem cell23_1431761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_1431761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431761 prefixEnd_1431761 := by exact prefixLift 1431761
  have htrace : WordTrace (prefixWord ++ tailWord_1431761) baseStart_1431761 baseEnd_1431761 := by
    simpa [prefixWord, tailWord_1431761, baseEnd_1431761] using wordTrace_append hprefix tailTrace_1431761
  have hstable : (prefixWord ++ tailWord_1431761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431761).length < 2 ^ (prefixWord ++ tailWord_1431761).sum := by decide
  have hdescent : baseEnd_1431761 < baseStart_1431761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431789 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1431789 : Nat := 118140960795 + 1431789 * 2 ^ 59
def prefixEnd_1431789 : Nat := 4983230072969 + 3 ^ 40 * 1431789 * 2
def baseEnd_1431789 : Nat := 735195952820403852652829

theorem tailTrace_1431789 : CollatzResearch.WordTrace tailWord_1431789 prefixEnd_1431789 735195952820403852652829 := by
  unfold tailWord_1431789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52221635009880457938274421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34814423339920305292182947 52221635009880457938274421)
  ·
    refine ⟨4895778282176292931713227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52221635009880457938274421 4895778282176292931713227)
    ·
      refine ⟨7343667423264439397569841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895778282176292931713227 7343667423264439397569841)
      ·
        refine ⟨5507750567448329548177381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7343667423264439397569841 5507750567448329548177381)
        ·
          refine ⟨1032703231396561790283259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5507750567448329548177381 1032703231396561790283259)
          ·
            refine ⟨1549054847094842685424889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032703231396561790283259 1549054847094842685424889)
            ·
              refine ⟨1161791135321132014068667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549054847094842685424889 1161791135321132014068667)
              ·
                refine ⟨1742686702981698021103001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161791135321132014068667 1742686702981698021103001)
                ·
                  refine ⟨1307015027236273515827251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742686702981698021103001 1307015027236273515827251)
                  ·
                    refine ⟨1960522540854410273740877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1307015027236273515827251 1960522540854410273740877)
                    ·
                      refine ⟨735195952820403852652829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1960522540854410273740877 735195952820403852652829)
                      ·
                        rfl

theorem cell23_1431789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1431789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431789 prefixEnd_1431789 := by exact prefixLift 1431789
  have htrace : WordTrace (prefixWord ++ tailWord_1431789) baseStart_1431789 baseEnd_1431789 := by
    simpa [prefixWord, tailWord_1431789, baseEnd_1431789] using wordTrace_append hprefix tailTrace_1431789
  have hstable : (prefixWord ++ tailWord_1431789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431789).length < 2 ^ (prefixWord ++ tailWord_1431789).sum := by decide
  have hdescent : baseEnd_1431789 < baseStart_1431789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431831 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 2, 5]
def baseStart_1431831 : Nat := 118140960795 + 1431831 * 2 ^ 59
def prefixEnd_1431831 : Nat := 4983230072969 + 3 ^ 40 * 1431831 * 2
def baseEnd_1431831 : Nat := 245072506335964229442545

theorem tailTrace_1431831 : CollatzResearch.WordTrace tailWord_1431831 prefixEnd_1431831 245072506335964229442545 := by
  unfold tailWord_1431831
  simp only [CollatzResearch.WordTrace]
  refine ⟨52223166875728299111303347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34815444583818866074202231 52223166875728299111303347)
  ·
    refine ⟨78334750313592448666955021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52223166875728299111303347 78334750313592448666955021)
    ·
      refine ⟨29375531367597168250108133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78334750313592448666955021 29375531367597168250108133)
      ·
        refine ⟨5507912131424469046895275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29375531367597168250108133 5507912131424469046895275)
        ·
          refine ⟨8261868197136703570342913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5507912131424469046895275 8261868197136703570342913)
          ·
            refine ⟨6196401147852527677757185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261868197136703570342913 6196401147852527677757185)
            ·
              refine ⟨4647300860889395758317889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196401147852527677757185 4647300860889395758317889)
              ·
                refine ⟨3485475645667046818738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647300860889395758317889 3485475645667046818738417)
                ·
                  refine ⟨2614106734250285114053813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3485475645667046818738417 2614106734250285114053813)
                  ·
                    refine ⟨245072506335964229442545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2614106734250285114053813 245072506335964229442545)
                    ·
                      rfl

theorem cell23_1431831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_1431831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431831 prefixEnd_1431831 := by exact prefixLift 1431831
  have htrace : WordTrace (prefixWord ++ tailWord_1431831) baseStart_1431831 baseEnd_1431831 := by
    simpa [prefixWord, tailWord_1431831, baseEnd_1431831] using wordTrace_append hprefix tailTrace_1431831
  have hstable : (prefixWord ++ tailWord_1431831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431831).length < 2 ^ (prefixWord ++ tailWord_1431831).sum := by decide
  have hdescent : baseEnd_1431831 < baseStart_1431831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431871 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_1431871 : Nat := 118140960795 + 1431871 * 2 ^ 59
def prefixEnd_1431871 : Nat := 4983230072969 + 3 ^ 40 * 1431871 * 2
def baseEnd_1431871 : Nat := 735238058234072531827451

theorem tailTrace_1431871 : CollatzResearch.WordTrace tailWord_1431871 prefixEnd_1431871 735238058234072531827451 := by
  unfold tailWord_1431871
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224625795583385942759467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34816417197055590628506311 52224625795583385942759467)
  ·
    refine ⟨78336938693375078914139201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52224625795583385942759467 78336938693375078914139201)
    ·
      refine ⟨58752704020031309185604401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78336938693375078914139201 58752704020031309185604401)
      ·
        refine ⟨44064528015023481889203301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58752704020031309185604401 44064528015023481889203301)
        ·
          refine ⟨8262099002816902854225619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44064528015023481889203301 8262099002816902854225619)
          ·
            refine ⟨12393148504225354281338429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262099002816902854225619 12393148504225354281338429)
            ·
              refine ⟨4647430689084507855501911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12393148504225354281338429 4647430689084507855501911)
              ·
                refine ⟨6971146033626761783252867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647430689084507855501911 6971146033626761783252867)
                ·
                  refine ⟨10456719050440142674879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971146033626761783252867 10456719050440142674879301)
                  ·
                    refine ⟨1960634821957526751539869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10456719050440142674879301 1960634821957526751539869)
                    ·
                      refine ⟨735238058234072531827451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1960634821957526751539869 735238058234072531827451)
                      ·
                        rfl

theorem cell23_1431871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_1431871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431871 prefixEnd_1431871 := by exact prefixLift 1431871
  have htrace : WordTrace (prefixWord ++ tailWord_1431871) baseStart_1431871 baseEnd_1431871 := by
    simpa [prefixWord, tailWord_1431871, baseEnd_1431871] using wordTrace_append hprefix tailTrace_1431871
  have hstable : (prefixWord ++ tailWord_1431871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431871).length < 2 ^ (prefixWord ++ tailWord_1431871).sum := by decide
  have hdescent : baseEnd_1431871 < baseStart_1431871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431908 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1431908 : Nat := 118140960795 + 1431908 * 2 ^ 59
def prefixEnd_1431908 : Nat := 4983230072969 + 3 ^ 40 * 1431908 * 2
def baseEnd_1431908 : Nat := 81695228557587654118309

theorem tailTrace_1431908 : CollatzResearch.WordTrace tailWord_1431908 prefixEnd_1431908 81695228557587654118309 := by
  unfold tailWord_1431908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26112987648224670630928189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34817316864299560841237585 26112987648224670630928189)
  ·
    refine ⟨9792370368084251486598071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26112987648224670630928189 9792370368084251486598071)
    ·
      refine ⟨14688555552126377229897107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792370368084251486598071 14688555552126377229897107)
      ·
        refine ⟨22032833328189565844845661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14688555552126377229897107 22032833328189565844845661)
        ·
          refine ⟨8262312498071087191817123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22032833328189565844845661 8262312498071087191817123)
          ·
            refine ⟨12393468747106630787725685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262312498071087191817123 12393468747106630787725685)
            ·
              refine ⟨1161887695041246636349283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12393468747106630787725685 1161887695041246636349283)
              ·
                refine ⟨1742831542561869954523925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161887695041246636349283 1742831542561869954523925)
                ·
                  refine ⟨81695228557587654118309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1742831542561869954523925 81695228557587654118309)
                  ·
                    rfl

theorem cell23_1431908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1431908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431908 prefixEnd_1431908 := by exact prefixLift 1431908
  have htrace : WordTrace (prefixWord ++ tailWord_1431908) baseStart_1431908 baseEnd_1431908 := by
    simpa [prefixWord, tailWord_1431908, baseEnd_1431908] using wordTrace_append hprefix tailTrace_1431908
  have hstable : (prefixWord ++ tailWord_1431908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431908).length < 2 ^ (prefixWord ++ tailWord_1431908).sum := by decide
  have hdescent : baseEnd_1431908 < baseStart_1431908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431941 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_1431941 : Nat := 118140960795 + 1431941 * 2 ^ 59
def prefixEnd_1431941 : Nat := 4983230072969 + 3 ^ 40 * 1431941 * 2
def baseEnd_1431941 : Nat := 735274001879887257952129

theorem tailTrace_1431941 : CollatzResearch.WordTrace tailWord_1431941 prefixEnd_1431941 735274001879887257952129 := by
  unfold tailWord_1431941
  simp only [CollatzResearch.WordTrace]
  refine ⟨52227178905329787897807677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818119270219858598538451 52227178905329787897807677)
  ·
    refine ⟨19585192089498670461677879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52227178905329787897807677 19585192089498670461677879)
    ·
      refine ⟨29377788134248005692516819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19585192089498670461677879 29377788134248005692516819)
      ·
        refine ⟨44066682201372008538775229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29377788134248005692516819 44066682201372008538775229)
        ·
          refine ⟨16525005825514503202040711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44066682201372008538775229 16525005825514503202040711)
          ·
            refine ⟨24787508738271754803061067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16525005825514503202040711 24787508738271754803061067)
            ·
              refine ⟨37181263107407632204591601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24787508738271754803061067 37181263107407632204591601)
              ·
                refine ⟨27885947330555724153443701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37181263107407632204591601 27885947330555724153443701)
                ·
                  refine ⟨2614307562239599139385347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27885947330555724153443701 2614307562239599139385347)
                  ·
                    refine ⟨3921461343359398709078021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614307562239599139385347 3921461343359398709078021)
                    ·
                      refine ⟨735274001879887257952129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3921461343359398709078021 735274001879887257952129)
                      ·
                        rfl

theorem cell23_1431941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_1431941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431941 prefixEnd_1431941 := by exact prefixLift 1431941
  have htrace : WordTrace (prefixWord ++ tailWord_1431941) baseStart_1431941 baseEnd_1431941 := by
    simpa [prefixWord, tailWord_1431941, baseEnd_1431941] using wordTrace_append hprefix tailTrace_1431941
  have hstable : (prefixWord ++ tailWord_1431941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431941).length < 2 ^ (prefixWord ++ tailWord_1431941).sum := by decide
  have hdescent : baseEnd_1431941 < baseStart_1431941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431945 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 2, 3, 2]
def baseStart_1431945 : Nat := 118140960795 + 1431945 * 2 ^ 59
def prefixEnd_1431945 : Nat := 4983230072969 + 3 ^ 40 * 1431945 * 2
def baseEnd_1431945 : Nat := 735276055802505242302111

theorem tailTrace_1431945 : CollatzResearch.WordTrace tailWord_1431945 prefixEnd_1431945 735276055802505242302111 := by
  unfold tailWord_1431945
  simp only [CollatzResearch.WordTrace]
  refine ⟨52227324797315296580953289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818216531543531053968859 52227324797315296580953289)
  ·
    refine ⟨39170493597986472435714967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52227324797315296580953289 39170493597986472435714967)
    ·
      refine ⟨58755740396979708653572451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39170493597986472435714967 58755740396979708653572451)
      ·
        refine ⟨88133610595469562980358677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58755740396979708653572451 88133610595469562980358677)
        ·
          refine ⟨4131262996662635764704313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88133610595469562980358677 4131262996662635764704313)
          ·
            refine ⟨3098447247496976823528235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131262996662635764704313 3098447247496976823528235)
            ·
              refine ⟨4647670871245465235292353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098447247496976823528235 4647670871245465235292353)
              ·
                refine ⟨3485753153434098926469265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647670871245465235292353 3485753153434098926469265)
                ·
                  refine ⟨2614314865075574194851949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3485753153434098926469265 2614314865075574194851949)
                  ·
                    refine ⟨980368074403340323069481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614314865075574194851949 980368074403340323069481)
                    ·
                      refine ⟨735276055802505242302111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980368074403340323069481 735276055802505242302111)
                      ·
                        rfl

theorem cell23_1431945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3, 2].length) (baseStart_1431945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431945 prefixEnd_1431945 := by exact prefixLift 1431945
  have htrace : WordTrace (prefixWord ++ tailWord_1431945) baseStart_1431945 baseEnd_1431945 := by
    simpa [prefixWord, tailWord_1431945, baseEnd_1431945] using wordTrace_append hprefix tailTrace_1431945
  have hstable : (prefixWord ++ tailWord_1431945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431945).length < 2 ^ (prefixWord ++ tailWord_1431945).sum := by decide
  have hdescent : baseEnd_1431945 < baseStart_1431945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431961 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1431961 : Nat := 118140960795 + 1431961 * 2 ^ 59
def prefixEnd_1431961 : Nat := 4983230072969 + 3 ^ 40 * 1431961 * 2
def baseEnd_1431961 : Nat := 735284271492977179702037

theorem tailTrace_1431961 : CollatzResearch.WordTrace tailWord_1431961 prefixEnd_1431961 735284271492977179702037 := by
  unfold tailWord_1431961
  simp only [CollatzResearch.WordTrace]
  refine ⟨52227908365257331313535737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818605576838220875690491 52227908365257331313535737)
  ·
    refine ⟨39170931273942998485151803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52227908365257331313535737 39170931273942998485151803)
    ·
      refine ⟨58756396910914497727727705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39170931273942998485151803 58756396910914497727727705)
      ·
        refine ⟨44067297683185873295795779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58756396910914497727727705 44067297683185873295795779)
        ·
          refine ⟨66100946524778809943693669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44067297683185873295795779 66100946524778809943693669)
          ·
            refine ⟨12393927473396026864442563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66100946524778809943693669 12393927473396026864442563)
            ·
              refine ⟨18590891210094040296663845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12393927473396026864442563 18590891210094040296663845)
              ·
                refine ⟨3485792101892632555624471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18590891210094040296663845 3485792101892632555624471)
                ·
                  refine ⟨5228688152838948833436707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485792101892632555624471 5228688152838948833436707)
                  ·
                    refine ⟨7843032229258423250155061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5228688152838948833436707 7843032229258423250155061)
                    ·
                      refine ⟨735284271492977179702037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7843032229258423250155061 735284271492977179702037)
                      ·
                        rfl

theorem cell23_1431961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1431961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431961 prefixEnd_1431961 := by exact prefixLift 1431961
  have htrace : WordTrace (prefixWord ++ tailWord_1431961) baseStart_1431961 baseEnd_1431961 := by
    simpa [prefixWord, tailWord_1431961, baseEnd_1431961] using wordTrace_append hprefix tailTrace_1431961
  have hstable : (prefixWord ++ tailWord_1431961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431961).length < 2 ^ (prefixWord ++ tailWord_1431961).sum := by decide
  have hdescent : baseEnd_1431961 < baseStart_1431961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431971 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1431971 : Nat := 118140960795 + 1431971 * 2 ^ 59
def prefixEnd_1431971 : Nat := 4983230072969 + 3 ^ 40 * 1431971 * 2
def baseEnd_1431971 : Nat := 735289406299522140576991

theorem tailTrace_1431971 : CollatzResearch.WordTrace tailWord_1431971 prefixEnd_1431971 735289406299522140576991 := by
  unfold tailWord_1431971
  simp only [CollatzResearch.WordTrace]
  refine ⟨52228273095221103021399767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818848730147402014266511 52228273095221103021399767)
  ·
    refine ⟨78342409642831654532099651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52228273095221103021399767 78342409642831654532099651)
    ·
      refine ⟨117513614464247481798149477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78342409642831654532099651 117513614464247481798149477)
      ·
        refine ⟨22033802712046402837153027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117513614464247481798149477 22033802712046402837153027)
        ·
          refine ⟨33050704068069604255729541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22033802712046402837153027 33050704068069604255729541)
          ·
            refine ⟨6197007012763050797949289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33050704068069604255729541 6197007012763050797949289)
            ·
              refine ⟨4647755259572288098461967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197007012763050797949289 4647755259572288098461967)
              ·
                refine ⟨6971632889358432147692951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647755259572288098461967 6971632889358432147692951)
                ·
                  refine ⟨10457449334037648221539427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971632889358432147692951 10457449334037648221539427)
                  ·
                    refine ⟨15686174001056472332309141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10457449334037648221539427 15686174001056472332309141)
                    ·
                      refine ⟨735289406299522140576991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15686174001056472332309141 735289406299522140576991)
                      ·
                        rfl

theorem cell23_1431971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1431971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431971 prefixEnd_1431971 := by exact prefixLift 1431971
  have htrace : WordTrace (prefixWord ++ tailWord_1431971) baseStart_1431971 baseEnd_1431971 := by
    simpa [prefixWord, tailWord_1431971, baseEnd_1431971] using wordTrace_append hprefix tailTrace_1431971
  have hstable : (prefixWord ++ tailWord_1431971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431971).length < 2 ^ (prefixWord ++ tailWord_1431971).sum := by decide
  have hdescent : baseEnd_1431971 < baseStart_1431971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431975 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1431975 : Nat := 118140960795 + 1431975 * 2 ^ 59
def prefixEnd_1431975 : Nat := 4983230072969 + 3 ^ 40 * 1431975 * 2
def baseEnd_1431975 : Nat := 735291460222140124926973

theorem tailTrace_1431975 : CollatzResearch.WordTrace tailWord_1431975 prefixEnd_1431975 735291460222140124926973 := by
  unfold tailWord_1431975
  simp only [CollatzResearch.WordTrace]
  refine ⟨52228418987206611704545379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34818945991471074469696919 52228418987206611704545379)
  ·
    refine ⟨78342628480809917556818069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52228418987206611704545379 78342628480809917556818069)
    ·
      refine ⟨3672310710037964885475847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78342628480809917556818069 3672310710037964885475847)
      ·
        refine ⟨5508466065056947328213771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672310710037964885475847 5508466065056947328213771)
        ·
          refine ⟨8262699097585420992320657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508466065056947328213771 8262699097585420992320657)
          ·
            refine ⟨6197024323189065744240493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8262699097585420992320657 6197024323189065744240493)
            ·
              refine ⟨2323884121195899654090185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6197024323189065744240493 2323884121195899654090185)
              ·
                refine ⟨1742913090896924740567639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323884121195899654090185 1742913090896924740567639)
                ·
                  refine ⟨2614369636345387110851459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742913090896924740567639 2614369636345387110851459)
                  ·
                    refine ⟨3921554454518080666277189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614369636345387110851459 3921554454518080666277189)
                    ·
                      refine ⟨735291460222140124926973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3921554454518080666277189 735291460222140124926973)
                      ·
                        rfl

theorem cell23_1431975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1431975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431975 prefixEnd_1431975 := by exact prefixLift 1431975
  have htrace : WordTrace (prefixWord ++ tailWord_1431975) baseStart_1431975 baseEnd_1431975 := by
    simpa [prefixWord, tailWord_1431975, baseEnd_1431975] using wordTrace_append hprefix tailTrace_1431975
  have hstable : (prefixWord ++ tailWord_1431975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431975).length < 2 ^ (prefixWord ++ tailWord_1431975).sum := by decide
  have hdescent : baseEnd_1431975 < baseStart_1431975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431992 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_1431992 : Nat := 118140960795 + 1431992 * 2 ^ 59
def prefixEnd_1431992 : Nat := 4983230072969 + 3 ^ 40 * 1431992 * 2
def baseEnd_1431992 : Nat := 735300189393266558414395

theorem tailTrace_1431992 : CollatzResearch.WordTrace tailWord_1431992 prefixEnd_1431992 735300189393266558414395 := by
  unfold tailWord_1431992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114519514072511803957115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34819359352096682405276153 26114519514072511803957115)
  ·
    refine ⟨39171779271108767705935673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26114519514072511803957115 39171779271108767705935673)
    ·
      refine ⟨29378834453331575779451755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39171779271108767705935673 29378834453331575779451755)
      ·
        refine ⟨44068251679997363669177633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29378834453331575779451755 44068251679997363669177633)
        ·
          refine ⟨33051188759998022751883225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44068251679997363669177633 33051188759998022751883225)
          ·
            refine ⟨24788391569998517063912419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33051188759998022751883225 24788391569998517063912419)
            ·
              refine ⟨37182587354997775595868629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24788391569998517063912419 37182587354997775595868629)
              ·
                refine ⟨871466891132760365528171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37182587354997775595868629 871466891132760365528171)
                ·
                  refine ⟨1307200336699140548292257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871466891132760365528171 1307200336699140548292257)
                  ·
                    refine ⟨980400252524355411219193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307200336699140548292257 980400252524355411219193)
                    ·
                      refine ⟨735300189393266558414395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980400252524355411219193 735300189393266558414395)
                      ·
                        rfl

theorem cell23_1431992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_1431992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1431992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1431992 prefixEnd_1431992 := by exact prefixLift 1431992
  have htrace : WordTrace (prefixWord ++ tailWord_1431992) baseStart_1431992 baseEnd_1431992 := by
    simpa [prefixWord, tailWord_1431992, baseEnd_1431992] using wordTrace_append hprefix tailTrace_1431992
  have hstable : (prefixWord ++ tailWord_1431992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431992).length < 2 ^ (prefixWord ++ tailWord_1431992).sum := by decide
  have hdescent : baseEnd_1431992 < baseStart_1431992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432009 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 1, 2, 2]
def baseStart_1432009 : Nat := 118140960795 + 1432009 * 2 ^ 59
def prefixEnd_1432009 : Nat := 4983230072969 + 3 ^ 40 * 1432009 * 2
def baseEnd_1432009 : Nat := 735308918564392991901817

theorem tailTrace_1432009 : CollatzResearch.WordTrace tailWord_1432009 prefixEnd_1432009 735308918564392991901817 := by
  unfold tailWord_1432009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52229659069083435511283081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34819772712722290340855387 52229659069083435511283081)
  ·
    refine ⟨39172244301812576633462311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52229659069083435511283081 39172244301812576633462311)
    ·
      refine ⟨58758366452718864950193467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39172244301812576633462311 58758366452718864950193467)
      ·
        refine ⟨88137549679078297425290201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58758366452718864950193467 88137549679078297425290201)
        ·
          refine ⟨66103162259308723068967651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88137549679078297425290201 66103162259308723068967651)
          ·
            refine ⟨99154743388963084603451477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66103162259308723068967651 99154743388963084603451477)
            ·
              refine ⟨1161969649089411147696697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 99154743388963084603451477 1161969649089411147696697)
              ·
                refine ⟨871477236817058360772523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161969649089411147696697 871477236817058360772523)
                ·
                  refine ⟨1307215855225587541158785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871477236817058360772523 1307215855225587541158785)
                  ·
                    refine ⟨980411891419190655869089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307215855225587541158785 980411891419190655869089)
                    ·
                      refine ⟨735308918564392991901817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980411891419190655869089 735308918564392991901817)
                      ·
                        rfl

theorem cell23_1432009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 2, 2].length) (baseStart_1432009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432009 prefixEnd_1432009 := by exact prefixLift 1432009
  have htrace : WordTrace (prefixWord ++ tailWord_1432009) baseStart_1432009 baseEnd_1432009 := by
    simpa [prefixWord, tailWord_1432009, baseEnd_1432009] using wordTrace_append hprefix tailTrace_1432009
  have hstable : (prefixWord ++ tailWord_1432009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432009).length < 2 ^ (prefixWord ++ tailWord_1432009).sum := by decide
  have hdescent : baseEnd_1432009 < baseStart_1432009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432025 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_1432025 : Nat := 118140960795 + 1432025 * 2 ^ 59
def prefixEnd_1432025 : Nat := 4983230072969 + 3 ^ 40 * 1432025 * 2
def baseEnd_1432025 : Nat := 735317134254864929301743

theorem tailTrace_1432025 : CollatzResearch.WordTrace tailWord_1432025 prefixEnd_1432025 735317134254864929301743 := by
  unfold tailWord_1432025
  simp only [CollatzResearch.WordTrace]
  refine ⟨52230242637025470243865529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34820161758016980162577019 52230242637025470243865529)
  ·
    refine ⟨39172681977769102682899147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52230242637025470243865529 39172681977769102682899147)
    ·
      refine ⟨58759022966653654024348721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39172681977769102682899147 58759022966653654024348721)
      ·
        refine ⟨44069267224990240518261541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58759022966653654024348721 44069267224990240518261541)
        ·
          refine ⟨8262987604685670097174039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44069267224990240518261541 8262987604685670097174039)
          ·
            refine ⟨12394481407028505145761059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262987604685670097174039 12394481407028505145761059)
            ·
              refine ⟨18591722110542757718641589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394481407028505145761059 18591722110542757718641589)
              ·
                refine ⟨1742973947863383536122649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18591722110542757718641589 1742973947863383536122649)
                ·
                  refine ⟨1307230460897537652091987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742973947863383536122649 1307230460897537652091987)
                  ·
                    refine ⟨1960845691346306478137981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1307230460897537652091987 1960845691346306478137981)
                    ·
                      refine ⟨735317134254864929301743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1960845691346306478137981 735317134254864929301743)
                      ·
                        rfl

theorem cell23_1432025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_1432025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432025 prefixEnd_1432025 := by exact prefixLift 1432025
  have htrace : WordTrace (prefixWord ++ tailWord_1432025) baseStart_1432025 baseEnd_1432025 := by
    simpa [prefixWord, tailWord_1432025, baseEnd_1432025] using wordTrace_append hprefix tailTrace_1432025
  have hstable : (prefixWord ++ tailWord_1432025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432025).length < 2 ^ (prefixWord ++ tailWord_1432025).sum := by decide
  have hdescent : baseEnd_1432025 < baseStart_1432025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432051 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_1432051 : Nat := 118140960795 + 1432051 * 2 ^ 59
def prefixEnd_1432051 : Nat := 4983230072969 + 3 ^ 40 * 1432051 * 2
def baseEnd_1432051 : Nat := 735330484751881827576623

theorem tailTrace_1432051 : CollatzResearch.WordTrace tailWord_1432051 prefixEnd_1432051 735330484751881827576623 := by
  unfold tailWord_1432051
  simp only [CollatzResearch.WordTrace]
  refine ⟨52231190934931276684312007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34820793956620851122874671 52231190934931276684312007)
  ·
    refine ⟨78346786402396915026468011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52231190934931276684312007 78346786402396915026468011)
    ·
      refine ⟨117520179603595372539702017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78346786402396915026468011 117520179603595372539702017)
      ·
        refine ⟨88140134702696529404776513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117520179603595372539702017 88140134702696529404776513)
        ·
          refine ⟨66105101027022397053582385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88140134702696529404776513 66105101027022397053582385)
          ·
            refine ⟨49578825770266797790186789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66105101027022397053582385 49578825770266797790186789)
            ·
              refine ⟨9296029831925024585660023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49578825770266797790186789 9296029831925024585660023)
              ·
                refine ⟨13944044747887536878490035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9296029831925024585660023 13944044747887536878490035)
                ·
                  refine ⟨20916067121831305317735053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13944044747887536878490035 20916067121831305317735053)
                  ·
                    refine ⟨7843525170686739494150645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20916067121831305317735053 7843525170686739494150645)
                    ·
                      refine ⟨735330484751881827576623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7843525170686739494150645 735330484751881827576623)
                      ·
                        rfl

theorem cell23_1432051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_1432051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432051 prefixEnd_1432051 := by exact prefixLift 1432051
  have htrace : WordTrace (prefixWord ++ tailWord_1432051) baseStart_1432051 baseEnd_1432051 := by
    simpa [prefixWord, tailWord_1432051, baseEnd_1432051] using wordTrace_append hprefix tailTrace_1432051
  have hstable : (prefixWord ++ tailWord_1432051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432051).length < 2 ^ (prefixWord ++ tailWord_1432051).sum := by decide
  have hdescent : baseEnd_1432051 < baseStart_1432051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432088 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 7]
def baseStart_1432088 : Nat := 118140960795 + 1432088 * 2 ^ 59
def prefixEnd_1432088 : Nat := 4983230072969 + 3 ^ 40 * 1432088 * 2
def baseEnd_1432088 : Nat := 81705498170677575868217

theorem tailTrace_1432088 : CollatzResearch.WordTrace tailWord_1432088 prefixEnd_1432088 81705498170677575868217 := by
  unfold tailWord_1432088
  simp only [CollatzResearch.WordTrace]
  refine ⟨26116270217898616001704459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34821693623864821335605945 26116270217898616001704459)
  ·
    refine ⟨39174405326847924002556689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26116270217898616001704459 39174405326847924002556689)
    ·
      refine ⟨29380803995135943001917517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39174405326847924002556689 29380803995135943001917517)
      ·
        refine ⟨11017801498175978625719069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29380803995135943001917517 11017801498175978625719069)
        ·
          refine ⟨4131675561815991984644651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11017801498175978625719069 4131675561815991984644651)
          ·
            refine ⟨6197513342723987976966977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131675561815991984644651 6197513342723987976966977)
            ·
              refine ⟨4648135007042990982725233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197513342723987976966977 4648135007042990982725233)
              ·
                refine ⟨3486101255282243237043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648135007042990982725233 3486101255282243237043925)
                ·
                  refine ⟨81705498170677575868217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3486101255282243237043925 81705498170677575868217)
                  ·
                    rfl

theorem cell23_1432088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_1432088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432088 prefixEnd_1432088 := by exact prefixLift 1432088
  have htrace : WordTrace (prefixWord ++ tailWord_1432088) baseStart_1432088 baseEnd_1432088 := by
    simpa [prefixWord, tailWord_1432088, baseEnd_1432088] using wordTrace_append hprefix tailTrace_1432088
  have hstable : (prefixWord ++ tailWord_1432088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432088).length < 2 ^ (prefixWord ++ tailWord_1432088).sum := by decide
  have hdescent : baseEnd_1432088 < baseStart_1432088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_1432111 : Nat := 118140960795 + 1432111 * 2 ^ 59
def prefixEnd_1432111 : Nat := 4983230072969 + 3 ^ 40 * 1432111 * 2
def baseEnd_1432111 : Nat := 735361293591151592826347

theorem tailTrace_1432111 : CollatzResearch.WordTrace tailWord_1432111 prefixEnd_1432111 735361293591151592826347 := by
  unfold tailWord_1432111
  simp only [CollatzResearch.WordTrace]
  refine ⟨52233379314713906931496187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34822252876475937954330791 52233379314713906931496187)
  ·
    refine ⟨78350068972070860397244281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52233379314713906931496187 78350068972070860397244281)
    ·
      refine ⟨58762551729053145297933211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78350068972070860397244281 58762551729053145297933211)
      ·
        refine ⟨88143827593579717946899817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58762551729053145297933211 88143827593579717946899817)
        ·
          refine ⟨66107870695184788460174863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88143827593579717946899817 66107870695184788460174863)
          ·
            refine ⟨99161806042777182690262295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66107870695184788460174863 99161806042777182690262295)
            ·
              refine ⟨148742709064165774035393443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99161806042777182690262295 148742709064165774035393443)
              ·
                refine ⟨223114063596248661053090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148742709064165774035393443 223114063596248661053090165)
                ·
                  refine ⟨20916943462148311973727203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223114063596248661053090165 20916943462148311973727203)
                  ·
                    refine ⟨31375415193222467960590805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20916943462148311973727203 31375415193222467960590805)
                    ·
                      refine ⟨735361293591151592826347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31375415193222467960590805 735361293591151592826347)
                      ·
                        rfl

theorem cell23_1432111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_1432111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432111 prefixEnd_1432111 := by exact prefixLift 1432111
  have htrace : WordTrace (prefixWord ++ tailWord_1432111) baseStart_1432111 baseEnd_1432111 := by
    simpa [prefixWord, tailWord_1432111, baseEnd_1432111] using wordTrace_append hprefix tailTrace_1432111
  have hstable : (prefixWord ++ tailWord_1432111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432111).length < 2 ^ (prefixWord ++ tailWord_1432111).sum := by decide
  have hdescent : baseEnd_1432111 < baseStart_1432111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432122 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_1432122 : Nat := 118140960795 + 1432122 * 2 ^ 59
def prefixEnd_1432122 : Nat := 4983230072969 + 3 ^ 40 * 1432122 * 2
def baseEnd_1432122 : Nat := 81707437986483449976533

theorem tailTrace_1432122 : CollatzResearch.WordTrace tailWord_1432122 prefixEnd_1432122 81707437986483449976533 := by
  unfold tailWord_1432122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13058445129418513952536655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34822520345116037206764413 13058445129418513952536655)
  ·
    refine ⟨19587667694127770928804983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13058445129418513952536655 19587667694127770928804983)
    ·
      refine ⟨29381501541191656393207475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19587667694127770928804983 29381501541191656393207475)
      ·
        refine ⟨44072252311787484589811213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29381501541191656393207475 44072252311787484589811213)
        ·
          refine ⟨16527094616920306721179205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44072252311787484589811213 16527094616920306721179205)
          ·
            refine ⟨3098830240672557510221101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16527094616920306721179205 3098830240672557510221101)
            ·
              refine ⟨1162061340252209066332913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3098830240672557510221101 1162061340252209066332913)
              ·
                refine ⟨871546005189156799749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162061340252209066332913 871546005189156799749685)
                ·
                  refine ⟨81707437986483449976533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871546005189156799749685 81707437986483449976533)
                  ·
                    rfl

theorem cell23_1432122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_1432122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432122 prefixEnd_1432122 := by exact prefixLift 1432122
  have htrace : WordTrace (prefixWord ++ tailWord_1432122) baseStart_1432122 baseEnd_1432122 := by
    simpa [prefixWord, tailWord_1432122, baseEnd_1432122] using wordTrace_append hprefix tailTrace_1432122
  have hstable : (prefixWord ++ tailWord_1432122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432122).length < 2 ^ (prefixWord ++ tailWord_1432122).sum := by decide
  have hdescent : baseEnd_1432122 < baseStart_1432122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432175 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_1432175 : Nat := 118140960795 + 1432175 * 2 ^ 59
def prefixEnd_1432175 : Nat := 4983230072969 + 3 ^ 40 * 1432175 * 2
def baseEnd_1432175 : Nat := 735394156353039342426053

theorem tailTrace_1432175 : CollatzResearch.WordTrace tailWord_1432175 prefixEnd_1432175 735394156353039342426053 := by
  unfold tailWord_1432175
  simp only [CollatzResearch.WordTrace]
  refine ⟨52235713586482045861825979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34823809057654697241217319 52235713586482045861825979)
  ·
    refine ⟨78353570379723068792738969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52235713586482045861825979 78353570379723068792738969)
    ·
      refine ⟨58765177784792301594554227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78353570379723068792738969 58765177784792301594554227)
      ·
        refine ⟨88147766677188452391831341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58765177784792301594554227 88147766677188452391831341)
        ·
          refine ⟨33055412503945669646936753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88147766677188452391831341 33055412503945669646936753)
          ·
            refine ⟨24791559377959252235202565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33055412503945669646936753 24791559377959252235202565)
            ·
              refine ⟨4648417383367359794100481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24791559377959252235202565 4648417383367359794100481)
              ·
                refine ⟨3486313037525519845575361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648417383367359794100481 3486313037525519845575361)
                ·
                  refine ⟨2614734778144139884181521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486313037525519845575361 2614734778144139884181521)
                  ·
                    refine ⟨1961051083608104913136141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2614734778144139884181521 1961051083608104913136141)
                    ·
                      refine ⟨735394156353039342426053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1961051083608104913136141 735394156353039342426053)
                      ·
                        rfl

theorem cell23_1432175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_1432175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432175 prefixEnd_1432175 := by exact prefixLift 1432175
  have htrace : WordTrace (prefixWord ++ tailWord_1432175) baseStart_1432175 baseEnd_1432175 := by
    simpa [prefixWord, tailWord_1432175, baseEnd_1432175] using wordTrace_append hprefix tailTrace_1432175
  have hstable : (prefixWord ++ tailWord_1432175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432175).length < 2 ^ (prefixWord ++ tailWord_1432175).sum := by decide
  have hdescent : baseEnd_1432175 < baseStart_1432175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432239 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 1, 1, 3]
def baseStart_1432239 : Nat := 118140960795 + 1432239 * 2 ^ 59
def prefixEnd_1432239 : Nat := 4983230072969 + 3 ^ 40 * 1432239 * 2
def baseEnd_1432239 : Nat := 735427019114927092025759

theorem tailTrace_1432239 : CollatzResearch.WordTrace tailWord_1432239 prefixEnd_1432239 735427019114927092025759 := by
  unfold tailWord_1432239
  simp only [CollatzResearch.WordTrace]
  refine ⟨52238047858250184792155771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34825365238833456528103847 52238047858250184792155771)
  ·
    refine ⟨78357071787375277188233657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52238047858250184792155771 78357071787375277188233657)
    ·
      refine ⟨58767803840531457891175243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78357071787375277188233657 58767803840531457891175243)
      ·
        refine ⟨88151705760797186836762865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58767803840531457891175243 88151705760797186836762865)
        ·
          refine ⟨66113779320597890127572149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88151705760797186836762865 66113779320597890127572149)
          ·
            refine ⟨6198166811306052199459889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66113779320597890127572149 6198166811306052199459889)
            ·
              refine ⟨4648625108479539149594917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198166811306052199459889 4648625108479539149594917)
              ·
                refine ⟨871617207839913590549047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4648625108479539149594917 871617207839913590549047)
                ·
                  refine ⟨1307425811759870385823571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871617207839913590549047 1307425811759870385823571)
                  ·
                    refine ⟨1961138717639805578735357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1307425811759870385823571 1961138717639805578735357)
                    ·
                      refine ⟨735427019114927092025759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1961138717639805578735357 735427019114927092025759)
                      ·
                        rfl

theorem cell23_1432239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 1, 3].length) (baseStart_1432239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432239 prefixEnd_1432239 := by exact prefixLift 1432239
  have htrace : WordTrace (prefixWord ++ tailWord_1432239) baseStart_1432239 baseEnd_1432239 := by
    simpa [prefixWord, tailWord_1432239, baseEnd_1432239] using wordTrace_append hprefix tailTrace_1432239
  have hstable : (prefixWord ++ tailWord_1432239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432239).length < 2 ^ (prefixWord ++ tailWord_1432239).sum := by decide
  have hdescent : baseEnd_1432239 < baseStart_1432239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432246 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1432246 : Nat := 118140960795 + 1432246 * 2 ^ 59
def prefixEnd_1432246 : Nat := 4983230072969 + 3 ^ 40 * 1432246 * 2
def baseEnd_1432246 : Nat := 81714512608834284959803

theorem tailTrace_1432246 : CollatzResearch.WordTrace tailWord_1432246 prefixEnd_1432246 81714512608834284959803 := by
  unfold tailWord_1432246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264893948076551561728787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34825535446149883325107061 3264893948076551561728787)
  ·
    refine ⟨4897340922114827342593181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3264893948076551561728787 4897340922114827342593181)
    ·
      refine ⟨1836502845793060253472443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4897340922114827342593181 1836502845793060253472443)
      ·
        refine ⟨2754754268689590380208665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836502845793060253472443 2754754268689590380208665)
        ·
          refine ⟨2066065701517192785156499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754754268689590380208665 2066065701517192785156499)
          ·
            refine ⟨3099098552275789177734749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066065701517192785156499 3099098552275789177734749)
            ·
              refine ⟨1162161957103420941650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3099098552275789177734749 1162161957103420941650531)
              ·
                refine ⟨1743242935655131412475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162161957103420941650531 1743242935655131412475797)
                ·
                  refine ⟨81714512608834284959803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1743242935655131412475797 81714512608834284959803)
                  ·
                    rfl

theorem cell23_1432246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1432246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432246 prefixEnd_1432246 := by exact prefixLift 1432246
  have htrace : WordTrace (prefixWord ++ tailWord_1432246) baseStart_1432246 baseEnd_1432246 := by
    simpa [prefixWord, tailWord_1432246, baseEnd_1432246] using wordTrace_append hprefix tailTrace_1432246
  have hstable : (prefixWord ++ tailWord_1432246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432246).length < 2 ^ (prefixWord ++ tailWord_1432246).sum := by decide
  have hdescent : baseEnd_1432246 < baseStart_1432246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432255 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 6]
def baseStart_1432255 : Nat := 118140960795 + 1432255 * 2 ^ 59
def prefixEnd_1432255 : Nat := 4983230072969 + 3 ^ 40 * 1432255 * 2
def baseEnd_1432255 : Nat := 245145078268466343141895

theorem tailTrace_1432255 : CollatzResearch.WordTrace tailWord_1432255 prefixEnd_1432255 245145078268466343141895 := by
  unfold tailWord_1432255
  simp only [CollatzResearch.WordTrace]
  refine ⟨52238631426192219524738219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34825754284128146349825479 52238631426192219524738219)
  ·
    refine ⟨78357947139288329287107329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52238631426192219524738219 78357947139288329287107329)
    ·
      refine ⟨58768460354466246965330497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78357947139288329287107329 58768460354466246965330497)
      ·
        refine ⟨44076345265849685223997873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58768460354466246965330497 44076345265849685223997873)
        ·
          refine ⟨33057258949387263917998405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44076345265849685223997873 33057258949387263917998405)
          ·
            refine ⟨6198236053010111984624701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33057258949387263917998405 6198236053010111984624701)
            ·
              refine ⟨2324338519878791994234263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6198236053010111984624701 2324338519878791994234263)
              ·
                refine ⟨3486507779818187991351395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324338519878791994234263 3486507779818187991351395)
                ·
                  refine ⟨5229761669727281987027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486507779818187991351395 5229761669727281987027093)
                  ·
                    refine ⟨245145078268466343141895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5229761669727281987027093 245145078268466343141895)
                    ·
                      rfl

theorem cell23_1432255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_1432255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432255 prefixEnd_1432255 := by exact prefixLift 1432255
  have htrace : WordTrace (prefixWord ++ tailWord_1432255) baseStart_1432255 baseEnd_1432255 := by
    simpa [prefixWord, tailWord_1432255, baseEnd_1432255] using wordTrace_append hprefix tailTrace_1432255
  have hstable : (prefixWord ++ tailWord_1432255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432255).length < 2 ^ (prefixWord ++ tailWord_1432255).sum := by decide
  have hdescent : baseEnd_1432255 < baseStart_1432255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432282 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_1432282 : Nat := 118140960795 + 1432282 * 2 ^ 59
def prefixEnd_1432282 : Nat := 4983230072969 + 3 ^ 40 * 1432282 * 2
def baseEnd_1432282 : Nat := 735449098783070423788061

theorem tailTrace_1432282 : CollatzResearch.WordTrace tailWord_1432282 prefixEnd_1432282 735449098783070423788061 := by
  unfold tailWord_1432282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13059904049273600783992775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34826410798062935423980733 13059904049273600783992775)
  ·
    refine ⟨19589856073910401175989163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13059904049273600783992775 19589856073910401175989163)
    ·
      refine ⟨29384784110865601763983745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19589856073910401175989163 29384784110865601763983745)
      ·
        refine ⟨22038588083149201322987809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29384784110865601763983745 22038588083149201322987809)
        ·
          refine ⟨16528941062361900992240857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22038588083149201322987809 16528941062361900992240857)
          ·
            refine ⟨12396705796771425744180643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16528941062361900992240857 12396705796771425744180643)
            ·
              refine ⟨18595058695157138616270965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396705796771425744180643 18595058695157138616270965)
              ·
                refine ⟨1743286752670981745275403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18595058695157138616270965 1743286752670981745275403)
                ·
                  refine ⟨2614930129006472617913105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743286752670981745275403 2614930129006472617913105)
                  ·
                    refine ⟨1961197596754854463434829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2614930129006472617913105 1961197596754854463434829)
                    ·
                      refine ⟨735449098783070423788061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1961197596754854463434829 735449098783070423788061)
                      ·
                        rfl

theorem cell23_1432282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_1432282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432282 prefixEnd_1432282 := by exact prefixLift 1432282
  have htrace : WordTrace (prefixWord ++ tailWord_1432282) baseStart_1432282 baseEnd_1432282 := by
    simpa [prefixWord, tailWord_1432282, baseEnd_1432282] using wordTrace_append hprefix tailTrace_1432282
  have hstable : (prefixWord ++ tailWord_1432282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432282).length < 2 ^ (prefixWord ++ tailWord_1432282).sum := by decide
  have hdescent : baseEnd_1432282 < baseStart_1432282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432306 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_1432306 : Nat := 118140960795 + 1432306 * 2 ^ 59
def prefixEnd_1432306 : Nat := 4983230072969 + 3 ^ 40 * 1432306 * 2
def baseEnd_1432306 : Nat := 245153807439592776629317

theorem tailTrace_1432306 : CollatzResearch.WordTrace tailWord_1432306 prefixEnd_1432306 245153807439592776629317 := by
  unfold tailWord_1432306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060122887251863808711193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34826994366004970156563181 13060122887251863808711193)
  ·
    refine ⟨9795092165438897856533395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13060122887251863808711193 9795092165438897856533395)
    ·
      refine ⟨14692638248158346784800093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9795092165438897856533395 14692638248158346784800093)
      ·
        refine ⟨5509739343059380044300035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14692638248158346784800093 5509739343059380044300035)
        ·
          refine ⟨8264609014589070066450053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509739343059380044300035 8264609014589070066450053)
          ·
            refine ⟨1549614190235450637459385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8264609014589070066450053 1549614190235450637459385)
            ·
              refine ⟨1162210642676587978094539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549614190235450637459385 1162210642676587978094539)
              ·
                refine ⟨1743315964014881967141809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162210642676587978094539 1743315964014881967141809)
                ·
                  refine ⟨1307486973011161475356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1743315964014881967141809 1307486973011161475356357)
                  ·
                    refine ⟨245153807439592776629317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307486973011161475356357 245153807439592776629317)
                    ·
                      rfl

theorem cell23_1432306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_1432306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432306 prefixEnd_1432306 := by exact prefixLift 1432306
  have htrace : WordTrace (prefixWord ++ tailWord_1432306) baseStart_1432306 baseEnd_1432306 := by
    simpa [prefixWord, tailWord_1432306, baseEnd_1432306] using wordTrace_append hprefix tailTrace_1432306
  have hstable : (prefixWord ++ tailWord_1432306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432306).length < 2 ^ (prefixWord ++ tailWord_1432306).sum := by decide
  have hdescent : baseEnd_1432306 < baseStart_1432306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432369 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_1432369 : Nat := 118140960795 + 1432369 * 2 ^ 59
def prefixEnd_1432369 : Nat := 4983230072969 + 3 ^ 40 * 1432369 * 2
def baseEnd_1432369 : Nat := 735493771600011583400161

theorem tailTrace_1432369 : CollatzResearch.WordTrace tailWord_1432369 prefixEnd_1432369 735493771600011583400161 := by
  unfold tailWord_1432369
  simp only [CollatzResearch.WordTrace]
  refine ⟨52242789347779216994388161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34828526231852811329592107 52242789347779216994388161)
  ·
    refine ⟨39182092010834412745791121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52242789347779216994388161 39182092010834412745791121)
    ·
      refine ⟨29386569008125809559343341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39182092010834412745791121 29386569008125809559343341)
      ·
        refine ⟨11019963378047178584753753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29386569008125809559343341 11019963378047178584753753)
        ·
          refine ⟨8264972533535383938565315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019963378047178584753753 8264972533535383938565315)
          ·
            refine ⟨12397458800303075907847973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264972533535383938565315 12397458800303075907847973)
            ·
              refine ⟨2324523525056826732721495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12397458800303075907847973 2324523525056826732721495)
              ·
                refine ⟨3486785287585240099082243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324523525056826732721495 3486785287585240099082243)
                ·
                  refine ⟨5230177931377860148623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486785287585240099082243 5230177931377860148623365)
                  ·
                    refine ⟨980658362133348777866881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230177931377860148623365 980658362133348777866881)
                    ·
                      refine ⟨735493771600011583400161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980658362133348777866881 735493771600011583400161)
                      ·
                        rfl

theorem cell23_1432369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_1432369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432369 prefixEnd_1432369 := by exact prefixLift 1432369
  have htrace : WordTrace (prefixWord ++ tailWord_1432369) baseStart_1432369 baseEnd_1432369 := by
    simpa [prefixWord, tailWord_1432369, baseEnd_1432369] using wordTrace_append hprefix tailTrace_1432369
  have hstable : (prefixWord ++ tailWord_1432369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432369).length < 2 ^ (prefixWord ++ tailWord_1432369).sum := by decide
  have hdescent : baseEnd_1432369 < baseStart_1432369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432375 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 7]
def baseStart_1432375 : Nat := 118140960795 + 1432375 * 2 ^ 59
def prefixEnd_1432375 : Nat := 4983230072969 + 3 ^ 40 * 1432375 * 2
def baseEnd_1432375 : Nat := 81721872498215395547237

theorem tailTrace_1432375 : CollatzResearch.WordTrace tailWord_1432375 prefixEnd_1432375 81721872498215395547237 := by
  unfold tailWord_1432375
  simp only [CollatzResearch.WordTrace]
  refine ⟨52243008185757480019106579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34828672123838320012737719 52243008185757480019106579)
  ·
    refine ⟨78364512278636220028659869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52243008185757480019106579 78364512278636220028659869)
    ·
      refine ⟨29386692104488582510747451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78364512278636220028659869 29386692104488582510747451)
      ·
        refine ⟨44080038156732873766121177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29386692104488582510747451 44080038156732873766121177)
        ·
          refine ⟨33060028617549655324590883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44080038156732873766121177 33060028617549655324590883)
          ·
            refine ⟨49590042926324482986886325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33060028617549655324590883 49590042926324482986886325)
            ·
              refine ⟨4649066524342920280020593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49590042926324482986886325 4649066524342920280020593)
              ·
                refine ⟨3486799893257190210015445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649066524342920280020593 3486799893257190210015445)
                ·
                  refine ⟨81721872498215395547237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3486799893257190210015445 81721872498215395547237)
                  ·
                    rfl

theorem cell23_1432375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 7].length) (baseStart_1432375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432375 prefixEnd_1432375 := by exact prefixLift 1432375
  have htrace : WordTrace (prefixWord ++ tailWord_1432375) baseStart_1432375 baseEnd_1432375 := by
    simpa [prefixWord, tailWord_1432375, baseEnd_1432375] using wordTrace_append hprefix tailTrace_1432375
  have hstable : (prefixWord ++ tailWord_1432375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432375).length < 2 ^ (prefixWord ++ tailWord_1432375).sum := by decide
  have hdescent : baseEnd_1432375 < baseStart_1432375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432390 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1432390 : Nat := 118140960795 + 1432390 * 2 ^ 59
def prefixEnd_1432390 : Nat := 4983230072969 + 3 ^ 40 * 1432390 * 2
def baseEnd_1432390 : Nat := 735504554693756001237565

theorem tailTrace_1432390 : CollatzResearch.WordTrace tailWord_1432390 prefixEnd_1432390 735504554693756001237565 := by
  unfold tailWord_1432390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632611102521973049403207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34829036853802091720601749 1632611102521973049403207)
  ·
    refine ⟨2448916653782959574104811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632611102521973049403207 2448916653782959574104811)
    ·
      refine ⟨3673374980674439361157217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448916653782959574104811 3673374980674439361157217)
      ·
        refine ⟨2755031235505829520867913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3673374980674439361157217 2755031235505829520867913)
        ·
          refine ⟨2066273426629372140650935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755031235505829520867913 2066273426629372140650935)
          ·
            refine ⟨3099410139944058210976403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066273426629372140650935 3099410139944058210976403)
            ·
              refine ⟨4649115209916087316464605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099410139944058210976403 4649115209916087316464605)
              ·
                refine ⟨1743418203718532743674227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4649115209916087316464605 1743418203718532743674227)
                ·
                  refine ⟨2615127305577799115511341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743418203718532743674227 2615127305577799115511341)
                  ·
                    refine ⟨980672739591674668316753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2615127305577799115511341 980672739591674668316753)
                    ·
                      refine ⟨735504554693756001237565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980672739591674668316753 735504554693756001237565)
                      ·
                        rfl

theorem cell23_1432390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1432390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432390 prefixEnd_1432390 := by exact prefixLift 1432390
  have htrace : WordTrace (prefixWord ++ tailWord_1432390) baseStart_1432390 baseEnd_1432390 := by
    simpa [prefixWord, tailWord_1432390, baseEnd_1432390] using wordTrace_append hprefix tailTrace_1432390
  have hstable : (prefixWord ++ tailWord_1432390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432390).length < 2 ^ (prefixWord ++ tailWord_1432390).sum := by decide
  have hdescent : baseEnd_1432390 < baseStart_1432390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432402 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1432402 : Nat := 118140960795 + 1432402 * 2 ^ 59
def prefixEnd_1432402 : Nat := 4983230072969 + 3 ^ 40 * 1432402 * 2
def baseEnd_1432402 : Nat := 735510716461609954287509

theorem tailTrace_1432402 : CollatzResearch.WordTrace tailWord_1432402 prefixEnd_1432402 735510716461609954287509 := by
  unfold tailWord_1432402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060998239164915907584865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34829328637773109086892973 13060998239164915907584865)
  ·
    refine ⟨9795748679373686930688649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13060998239164915907584865 9795748679373686930688649)
    ·
      refine ⟨7346811509530265198016487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9795748679373686930688649 7346811509530265198016487)
      ·
        refine ⟨11020217264295397797024731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346811509530265198016487 11020217264295397797024731)
        ·
          refine ⟨16530325896443096695537097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020217264295397797024731 16530325896443096695537097)
          ·
            refine ⟨12397744422332322521652823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16530325896443096695537097 12397744422332322521652823)
            ·
              refine ⟨18596616633498483782479235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12397744422332322521652823 18596616633498483782479235)
              ·
                refine ⟨27894924950247725673718853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18596616633498483782479235 27894924950247725673718853)
                ·
                  refine ⟨5230298428171448563822285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27894924950247725673718853 5230298428171448563822285)
                  ·
                    refine ⟨1961361910564293211433357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230298428171448563822285 1961361910564293211433357)
                    ·
                      refine ⟨735510716461609954287509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1961361910564293211433357 735510716461609954287509)
                      ·
                        rfl

theorem cell23_1432402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1432402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432402 prefixEnd_1432402 := by exact prefixLift 1432402
  have htrace : WordTrace (prefixWord ++ tailWord_1432402) baseStart_1432402 baseEnd_1432402 := by
    simpa [prefixWord, tailWord_1432402, baseEnd_1432402] using wordTrace_append hprefix tailTrace_1432402
  have hstable : (prefixWord ++ tailWord_1432402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432402).length < 2 ^ (prefixWord ++ tailWord_1432402).sum := by decide
  have hdescent : baseEnd_1432402 < baseStart_1432402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432415 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1432415 : Nat := 118140960795 + 1432415 * 2 ^ 59
def prefixEnd_1432415 : Nat := 4983230072969 + 3 ^ 40 * 1432415 * 2
def baseEnd_1432415 : Nat := 735517391710118403424949

theorem tailTrace_1432415 : CollatzResearch.WordTrace tailWord_1432415 prefixEnd_1432415 735517391710118403424949 := by
  unfold tailWord_1432415
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244467105612566850562699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34829644737075044567041799 52244467105612566850562699)
  ·
    refine ⟨78366700658418850275844049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52244467105612566850562699 78366700658418850275844049)
    ·
      refine ⟨58775025493814137706883037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78366700658418850275844049 58775025493814137706883037)
      ·
        refine ⟨22040634560180301640081139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58775025493814137706883037 22040634560180301640081139)
        ·
          refine ⟨33060951840270452460121709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22040634560180301640081139 33060951840270452460121709)
          ·
            refine ⟨12397856940101419672545641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33060951840270452460121709 12397856940101419672545641)
            ·
              refine ⟨9298392705076064754409231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12397856940101419672545641 9298392705076064754409231)
              ·
                refine ⟨13947589057614097131613847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298392705076064754409231 13947589057614097131613847)
                ·
                  refine ⟨20921383586421145697420771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13947589057614097131613847 20921383586421145697420771)
                  ·
                    refine ⟨31382075379631718546131157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20921383586421145697420771 31382075379631718546131157)
                    ·
                      refine ⟨735517391710118403424949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31382075379631718546131157 735517391710118403424949)
                      ·
                        rfl

theorem cell23_1432415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1432415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432415 prefixEnd_1432415 := by exact prefixLift 1432415
  have htrace : WordTrace (prefixWord ++ tailWord_1432415) baseStart_1432415 baseEnd_1432415 := by
    simpa [prefixWord, tailWord_1432415, baseEnd_1432415] using wordTrace_append hprefix tailTrace_1432415
  have hstable : (prefixWord ++ tailWord_1432415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432415).length < 2 ^ (prefixWord ++ tailWord_1432415).sum := by decide
  have hdescent : baseEnd_1432415 < baseStart_1432415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432442 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_1432442 : Nat := 118140960795 + 1432442 * 2 ^ 59
def prefixEnd_1432442 : Nat := 4983230072969 + 3 ^ 40 * 1432442 * 2
def baseEnd_1432442 : Nat := 735531255687789797787325

theorem tailTrace_1432442 : CollatzResearch.WordTrace tailWord_1432442 prefixEnd_1432442 735531255687789797787325 := by
  unfold tailWord_1432442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061362969128687615448895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34830301251009833641197053 13061362969128687615448895)
  ·
    refine ⟨19592044453693031423173343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13061362969128687615448895 19592044453693031423173343)
    ·
      refine ⟨29388066680539547134760015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19592044453693031423173343 29388066680539547134760015)
      ·
        refine ⟨44082100020809320702140023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29388066680539547134760015 44082100020809320702140023)
        ·
          refine ⟨66123150031213981053210035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44082100020809320702140023 66123150031213981053210035)
          ·
            refine ⟨99184725046820971579815053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66123150031213981053210035 99184725046820971579815053)
            ·
              refine ⟨37194271892557864342430645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99184725046820971579815053 37194271892557864342430645)
              ·
                refine ⟨3486962989927299782102873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37194271892557864342430645 3486962989927299782102873)
                ·
                  refine ⟨2615222242445474836577155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486962989927299782102873 2615222242445474836577155)
                  ·
                    refine ⟨3922833363668212254865733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615222242445474836577155 3922833363668212254865733)
                    ·
                      refine ⟨735531255687789797787325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3922833363668212254865733 735531255687789797787325)
                      ·
                        rfl

theorem cell23_1432442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_1432442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432442 prefixEnd_1432442 := by exact prefixLift 1432442
  have htrace : WordTrace (prefixWord ++ tailWord_1432442) baseStart_1432442 baseEnd_1432442 := by
    simpa [prefixWord, tailWord_1432442, baseEnd_1432442] using wordTrace_append hprefix tailTrace_1432442
  have hstable : (prefixWord ++ tailWord_1432442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432442).length < 2 ^ (prefixWord ++ tailWord_1432442).sum := by decide
  have hdescent : baseEnd_1432442 < baseStart_1432442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432469 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1432469 : Nat := 118140960795 + 1432469 * 2 ^ 59
def prefixEnd_1432469 : Nat := 4983230072969 + 3 ^ 40 * 1432469 * 2
def baseEnd_1432469 : Nat := 245181706555153730716567

theorem tailTrace_1432469 : CollatzResearch.WordTrace tailWord_1432469 prefixEnd_1432469 245181706555153730716567 := by
  unfold tailWord_1432469
  simp only [CollatzResearch.WordTrace]
  refine ⟨52246436647416934073028461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34830957764944622715352307 52246436647416934073028461)
  ·
    refine ⟨19592413742781350277385673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52246436647416934073028461 19592413742781350277385673)
    ·
      refine ⟨14694310307086012708039255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19592413742781350277385673 14694310307086012708039255)
      ·
        refine ⟨22041465460629019062058883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694310307086012708039255 22041465460629019062058883)
        ·
          refine ⟨33062198190943528593088325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041465460629019062058883 33062198190943528593088325)
          ·
            refine ⟨6199162160801911611204061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33062198190943528593088325 6199162160801911611204061)
            ·
              refine ⟨2324685810300716854201523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6199162160801911611204061 2324685810300716854201523)
              ·
                refine ⟨3487028715451075281302285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324685810300716854201523 3487028715451075281302285)
                ·
                  refine ⟨1307635768294153230488357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3487028715451075281302285 1307635768294153230488357)
                  ·
                    refine ⟨245181706555153730716567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307635768294153230488357 245181706555153730716567)
                    ·
                      rfl

theorem cell23_1432469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1432469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432469 prefixEnd_1432469 := by exact prefixLift 1432469
  have htrace : WordTrace (prefixWord ++ tailWord_1432469) baseStart_1432469 baseEnd_1432469 := by
    simpa [prefixWord, tailWord_1432469, baseEnd_1432469] using wordTrace_append hprefix tailTrace_1432469
  have hstable : (prefixWord ++ tailWord_1432469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432469).length < 2 ^ (prefixWord ++ tailWord_1432469).sum := by decide
  have hdescent : baseEnd_1432469 < baseStart_1432469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432493 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1432493 : Nat := 118140960795 + 1432493 * 2 ^ 59
def prefixEnd_1432493 : Nat := 4983230072969 + 3 ^ 40 * 1432493 * 2
def baseEnd_1432493 : Nat := 735557443201169098249591

theorem tailTrace_1432493 : CollatzResearch.WordTrace tailWord_1432493 prefixEnd_1432493 735557443201169098249591 := by
  unfold tailWord_1432493
  simp only [CollatzResearch.WordTrace]
  refine ⟨52247311999329986171902133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34831541332886657447934755 52247311999329986171902133)
  ·
    refine ⟨4898185499937186203615825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52247311999329986171902133 4898185499937186203615825)
    ·
      refine ⟨3673639124952889652711869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4898185499937186203615825 3673639124952889652711869)
      ·
        refine ⟨1377614671857333619766951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3673639124952889652711869 1377614671857333619766951)
        ·
          refine ⟨2066422007786000429650427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377614671857333619766951 2066422007786000429650427)
          ·
            refine ⟨3099633011679000644475641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066422007786000429650427 3099633011679000644475641)
            ·
              refine ⟨2324724758759250483356731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099633011679000644475641 2324724758759250483356731)
              ·
                refine ⟨3487087138138875725035097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324724758759250483356731 3487087138138875725035097)
                ·
                  refine ⟨2615315353604156793776323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487087138138875725035097 2615315353604156793776323)
                  ·
                    refine ⟨3922973030406235190664485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615315353604156793776323 3922973030406235190664485)
                    ·
                      refine ⟨735557443201169098249591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3922973030406235190664485 735557443201169098249591)
                      ·
                        rfl

theorem cell23_1432493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1432493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432493 prefixEnd_1432493 := by exact prefixLift 1432493
  have htrace : WordTrace (prefixWord ++ tailWord_1432493) baseStart_1432493 baseEnd_1432493 := by
    simpa [prefixWord, tailWord_1432493, baseEnd_1432493] using wordTrace_append hprefix tailTrace_1432493
  have hstable : (prefixWord ++ tailWord_1432493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432493).length < 2 ^ (prefixWord ++ tailWord_1432493).sum := by decide
  have hdescent : baseEnd_1432493 < baseStart_1432493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432520 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1432520 : Nat := 118140960795 + 1432520 * 2 ^ 59
def prefixEnd_1432520 : Nat := 4983230072969 + 3 ^ 40 * 1432520 * 2
def baseEnd_1432520 : Nat := 245190435726280164203989

theorem tailTrace_1432520 : CollatzResearch.WordTrace tailWord_1432520 prefixEnd_1432520 245190435726280164203989 := by
  unfold tailWord_1432520
  simp only [CollatzResearch.WordTrace]
  refine ⟨26124148385116084891567507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34832197846821446522090009 26124148385116084891567507)
  ·
    refine ⟨39186222577674127337351261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26124148385116084891567507 39186222577674127337351261)
    ·
      refine ⟨14694833466627797751506723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39186222577674127337351261 14694833466627797751506723)
      ·
        refine ⟨22042250199941696627260085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694833466627797751506723 22042250199941696627260085)
        ·
          refine ⟨2066460956244534058805633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22042250199941696627260085 2066460956244534058805633)
          ·
            refine ⟨1549845717183400544104225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066460956244534058805633 1549845717183400544104225)
            ·
              refine ⟨1162384287887550408078169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549845717183400544104225 1162384287887550408078169)
              ·
                refine ⟨871788215915662806058627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162384287887550408078169 871788215915662806058627)
                ·
                  refine ⟨1307682323873494209087941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871788215915662806058627 1307682323873494209087941)
                  ·
                    refine ⟨245190435726280164203989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307682323873494209087941 245190435726280164203989)
                    ·
                      rfl

theorem cell23_1432520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1432520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432520 prefixEnd_1432520 := by exact prefixLift 1432520
  have htrace : WordTrace (prefixWord ++ tailWord_1432520) baseStart_1432520 baseEnd_1432520 := by
    simpa [prefixWord, tailWord_1432520, baseEnd_1432520] using wordTrace_append hprefix tailTrace_1432520
  have hstable : (prefixWord ++ tailWord_1432520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432520).length < 2 ^ (prefixWord ++ tailWord_1432520).sum := by decide
  have hdescent : baseEnd_1432520 < baseStart_1432520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432546 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1432546 : Nat := 118140960795 + 1432546 * 2 ^ 59
def prefixEnd_1432546 : Nat := 4983230072969 + 3 ^ 40 * 1432546 * 2
def baseEnd_1432546 : Nat := 245194885891952463628949

theorem tailTrace_1432546 : CollatzResearch.WordTrace tailWord_1432546 prefixEnd_1432546 245194885891952463628949 := by
  unfold tailWord_1432546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062311267034494055895373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34832830045425317482387661 13062311267034494055895373)
  ·
    refine ⟨4898366725137935270960765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13062311267034494055895373 4898366725137935270960765)
    ·
      refine ⟨1836887521926725726610287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4898366725137935270960765 1836887521926725726610287)
      ·
        refine ⟨2755331282890088589915431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836887521926725726610287 2755331282890088589915431)
        ·
          refine ⟨4132996924335132884873147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755331282890088589915431 4132996924335132884873147)
          ·
            refine ⟨6199495386502699327309721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132996924335132884873147 6199495386502699327309721)
            ·
              refine ⟨4649621539877024495482291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6199495386502699327309721 4649621539877024495482291)
              ·
                refine ⟨6974432309815536743223437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649621539877024495482291 6974432309815536743223437)
                ·
                  refine ⟨2615412116180826278708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6974432309815536743223437 2615412116180826278708789)
                  ·
                    refine ⟨245194885891952463628949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2615412116180826278708789 245194885891952463628949)
                    ·
                      rfl

theorem cell23_1432546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1432546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432546 prefixEnd_1432546 := by exact prefixLift 1432546
  have htrace : WordTrace (prefixWord ++ tailWord_1432546) baseStart_1432546 baseEnd_1432546 := by
    simpa [prefixWord, tailWord_1432546, baseEnd_1432546] using wordTrace_append hprefix tailTrace_1432546
  have hstable : (prefixWord ++ tailWord_1432546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432546).length < 2 ^ (prefixWord ++ tailWord_1432546).sum := by decide
  have hdescent : baseEnd_1432546 < baseStart_1432546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432572 : List Nat := [2, 2, 2, 1, 2, 4, 10]
def baseStart_1432572 : Nat := 118140960795 + 1432572 * 2 ^ 59
def prefixEnd_1432572 : Nat := 4983230072969 + 3 ^ 40 * 1432572 * 2
def baseEnd_1432572 : Nat := 9081456891023139372367

theorem tailTrace_1432572 : CollatzResearch.WordTrace tailWord_1432572 prefixEnd_1432572 9081456891023139372367 := by
  unfold tailWord_1432572
  simp only [CollatzResearch.WordTrace]
  refine ⟨26125096683021891332013985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34833462244029188442685313 26125096683021891332013985)
  ·
    refine ⟨19593822512266418499010489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26125096683021891332013985 19593822512266418499010489)
    ·
      refine ⟨14695366884199813874257867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19593822512266418499010489 14695366884199813874257867)
      ·
        refine ⟨22043050326299720811386801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14695366884199813874257867 22043050326299720811386801)
        ·
          refine ⟨16532287744724790608540101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22043050326299720811386801 16532287744724790608540101)
          ·
            refine ⟨3099803952135898239101269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16532287744724790608540101 3099803952135898239101269)
            ·
              refine ⟨9081456891023139372367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3099803952135898239101269 9081456891023139372367)
              ·
                rfl

theorem cell23_1432572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 10].length) (baseStart_1432572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432572 prefixEnd_1432572 := by exact prefixLift 1432572
  have htrace : WordTrace (prefixWord ++ tailWord_1432572) baseStart_1432572 baseEnd_1432572 := by
    simpa [prefixWord, tailWord_1432572, baseEnd_1432572] using wordTrace_append hprefix tailTrace_1432572
  have hstable : (prefixWord ++ tailWord_1432572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432572).length < 2 ^ (prefixWord ++ tailWord_1432572).sum := by decide
  have hdescent : baseEnd_1432572 < baseStart_1432572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432583 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1432583 : Nat := 118140960795 + 1432583 * 2 ^ 59
def prefixEnd_1432583 : Nat := 4983230072969 + 3 ^ 40 * 1432583 * 2
def baseEnd_1432583 : Nat := 735603656460073746124177

theorem tailTrace_1432583 : CollatzResearch.WordTrace tailWord_1432583 prefixEnd_1432583 735603656460073746124177 := by
  unfold tailWord_1432583
  simp only [CollatzResearch.WordTrace]
  refine ⟨52250594569003931542678403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34833729712669287695118935 52250594569003931542678403)
  ·
    refine ⟨78375891853505897314017605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52250594569003931542678403 78375891853505897314017605)
    ·
      refine ⟨14695479722532355746378301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78375891853505897314017605 14695479722532355746378301)
      ·
        refine ⟨5510804895949633404891863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14695479722532355746378301 5510804895949633404891863)
        ·
          refine ⟨8266207343924450107337795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510804895949633404891863 8266207343924450107337795)
          ·
            refine ⟨12399311015886675161006693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266207343924450107337795 12399311015886675161006693)
            ·
              refine ⟨2324870815478751592688755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12399311015886675161006693 2324870815478751592688755)
              ·
                refine ⟨3487306223218127389033133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324870815478751592688755 3487306223218127389033133)
                ·
                  refine ⟨1307739833706797770887425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3487306223218127389033133 1307739833706797770887425)
                  ·
                    refine ⟨980804875280098328165569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307739833706797770887425 980804875280098328165569)
                    ·
                      refine ⟨735603656460073746124177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980804875280098328165569 735603656460073746124177)
                      ·
                        rfl

theorem cell23_1432583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1432583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432583 prefixEnd_1432583 := by exact prefixLift 1432583
  have htrace : WordTrace (prefixWord ++ tailWord_1432583) baseStart_1432583 baseEnd_1432583 := by
    simpa [prefixWord, tailWord_1432583, baseEnd_1432583] using wordTrace_append hprefix tailTrace_1432583
  have hstable : (prefixWord ++ tailWord_1432583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432583).length < 2 ^ (prefixWord ++ tailWord_1432583).sum := by decide
  have hdescent : baseEnd_1432583 < baseStart_1432583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432690 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_1432690 : Nat := 118140960795 + 1432690 * 2 ^ 59
def prefixEnd_1432690 : Nat := 4983230072969 + 3 ^ 40 * 1432690 * 2
def baseEnd_1432690 : Nat := 735658598890104827486185

theorem tailTrace_1432690 : CollatzResearch.WordTrace tailWord_1432690 prefixEnd_1432690 735658598890104827486185 := by
  unfold tailWord_1432690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063624294904072204205881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34836331453077525877882349 13063624294904072204205881)
  ·
    refine ⟨9797718221178054153154411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13063624294904072204205881 9797718221178054153154411)
    ·
      refine ⟨14696577331767081229731617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9797718221178054153154411 14696577331767081229731617)
      ·
        refine ⟨11022432998825310922298713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14696577331767081229731617 11022432998825310922298713)
        ·
          refine ⟨8266824749118983191724035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11022432998825310922298713 8266824749118983191724035)
          ·
            refine ⟨12400237123678474787586053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266824749118983191724035 12400237123678474787586053)
            ·
              refine ⟨2325044460689714022672385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12400237123678474787586053 2325044460689714022672385)
              ·
                refine ⟨1743783345517285517004289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325044460689714022672385 1743783345517285517004289)
                ·
                  refine ⟨1307837509137964137753217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1743783345517285517004289 1307837509137964137753217)
                  ·
                    refine ⟨980878131853473103314913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307837509137964137753217 980878131853473103314913)
                    ·
                      refine ⟨735658598890104827486185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 980878131853473103314913 735658598890104827486185)
                      ·
                        rfl

theorem cell23_1432690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_1432690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432690 prefixEnd_1432690 := by exact prefixLift 1432690
  have htrace : WordTrace (prefixWord ++ tailWord_1432690) baseStart_1432690 baseEnd_1432690 := by
    simpa [prefixWord, tailWord_1432690, baseEnd_1432690] using wordTrace_append hprefix tailTrace_1432690
  have hstable : (prefixWord ++ tailWord_1432690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432690).length < 2 ^ (prefixWord ++ tailWord_1432690).sum := by decide
  have hdescent : baseEnd_1432690 < baseStart_1432690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432759 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1432759 : Nat := 118140960795 + 1432759 * 2 ^ 59
def prefixEnd_1432759 : Nat := 4983230072969 + 3 ^ 40 * 1432759 * 2
def baseEnd_1432759 : Nat := 735694029055265057523367

theorem tailTrace_1432759 : CollatzResearch.WordTrace tailWord_1432759 prefixEnd_1432759 735694029055265057523367 := by
  unfold tailWord_1432759
  simp only [CollatzResearch.WordTrace]
  refine ⟨52257013816366313601085331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34838009210910875734056887 52257013816366313601085331)
  ·
    refine ⟨78385520724549470401627997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52257013816366313601085331 78385520724549470401627997)
    ·
      refine ⟨29394570271706051400610499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78385520724549470401627997 29394570271706051400610499)
      ·
        refine ⟨44091855407559077100915749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29394570271706051400610499 44091855407559077100915749)
        ·
          refine ⟨8267222888917326956421703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44091855407559077100915749 8267222888917326956421703)
          ·
            refine ⟨12400834333375990434632555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8267222888917326956421703 12400834333375990434632555)
            ·
              refine ⟨18601251500063985651948833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12400834333375990434632555 18601251500063985651948833)
              ·
                refine ⟨13950938625047989238961625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18601251500063985651948833 13950938625047989238961625)
                ·
                  refine ⟨10463203968785991929221219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13950938625047989238961625 10463203968785991929221219)
                  ·
                    refine ⟨15694805953178987893831829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10463203968785991929221219 15694805953178987893831829)
                    ·
                      refine ⟨735694029055265057523367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15694805953178987893831829 735694029055265057523367)
                      ·
                        rfl

theorem cell23_1432759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1432759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432759 prefixEnd_1432759 := by exact prefixLift 1432759
  have htrace : WordTrace (prefixWord ++ tailWord_1432759) baseStart_1432759 baseEnd_1432759 := by
    simpa [prefixWord, tailWord_1432759, baseEnd_1432759] using wordTrace_append hprefix tailTrace_1432759
  have hstable : (prefixWord ++ tailWord_1432759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432759).length < 2 ^ (prefixWord ++ tailWord_1432759).sum := by decide
  have hdescent : baseEnd_1432759 < baseStart_1432759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432807 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1432807 : Nat := 118140960795 + 1432807 * 2 ^ 59
def prefixEnd_1432807 : Nat := 4983230072969 + 3 ^ 40 * 1432807 * 2
def baseEnd_1432807 : Nat := 245239558708893623241049

theorem tailTrace_1432807 : CollatzResearch.WordTrace tailWord_1432807 prefixEnd_1432807 245239558708893623241049 := by
  unfold tailWord_1432807
  simp only [CollatzResearch.WordTrace]
  refine ⟨52258764520192417798832675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34839176346794945199221783 52258764520192417798832675)
  ·
    refine ⟨78388146780288626698249013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52258764520192417798832675 78388146780288626698249013)
    ·
      refine ⟨7348888760652058752960845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78388146780288626698249013 7348888760652058752960845)
      ·
        refine ⟨2755833285244522032360317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7348888760652058752960845 2755833285244522032360317)
        ·
          refine ⟨1033437481966695762135119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2755833285244522032360317 1033437481966695762135119)
          ·
            refine ⟨1550156222950043643202679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033437481966695762135119 1550156222950043643202679)
            ·
              refine ⟨2325234334425065464804019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550156222950043643202679 2325234334425065464804019)
              ·
                refine ⟨3487851501637598197206029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325234334425065464804019 3487851501637598197206029)
                ·
                  refine ⟨1307944313114099323952261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3487851501637598197206029 1307944313114099323952261)
                  ·
                    refine ⟨245239558708893623241049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307944313114099323952261 245239558708893623241049)
                    ·
                      rfl

theorem cell23_1432807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1432807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432807 prefixEnd_1432807 := by exact prefixLift 1432807
  have htrace : WordTrace (prefixWord ++ tailWord_1432807) baseStart_1432807 baseEnd_1432807 := by
    simpa [prefixWord, tailWord_1432807, baseEnd_1432807] using wordTrace_append hprefix tailTrace_1432807
  have hstable : (prefixWord ++ tailWord_1432807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432807).length < 2 ^ (prefixWord ++ tailWord_1432807).sum := by decide
  have hdescent : baseEnd_1432807 < baseStart_1432807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432833 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1432833 : Nat := 118140960795 + 1432833 * 2 ^ 59
def prefixEnd_1432833 : Nat := 4983230072969 + 3 ^ 40 * 1432833 * 2
def baseEnd_1432833 : Nat := 245244008874565922666009

theorem tailTrace_1432833 : CollatzResearch.WordTrace tailWord_1432833 prefixEnd_1432833 245244008874565922666009 := by
  unfold tailWord_1432833
  simp only [CollatzResearch.WordTrace]
  refine ⟨52259712818098224239279153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34839808545398816159519435 52259712818098224239279153)
  ·
    refine ⟨39194784613573668179459365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52259712818098224239279153 39194784613573668179459365)
    ·
      refine ⟨7349022115045062783648631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39194784613573668179459365 7349022115045062783648631)
      ·
        refine ⟨11023533172567594175472947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349022115045062783648631 11023533172567594175472947)
        ·
          refine ⟨16535299758851391263209421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023533172567594175472947 16535299758851391263209421)
          ·
            refine ⟨6200737409569271723703533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16535299758851391263209421 6200737409569271723703533)
            ·
              refine ⟨2325276528588476896388825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6200737409569271723703533 2325276528588476896388825)
              ·
                refine ⟨1743957396441357672291619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325276528588476896388825 1743957396441357672291619)
                ·
                  refine ⟨2615936094662036508437429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743957396441357672291619 2615936094662036508437429)
                  ·
                    refine ⟨245244008874565922666009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2615936094662036508437429 245244008874565922666009)
                    ·
                      rfl

theorem cell23_1432833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1432833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432833 prefixEnd_1432833 := by exact prefixLift 1432833
  have htrace : WordTrace (prefixWord ++ tailWord_1432833) baseStart_1432833 baseEnd_1432833 := by
    simpa [prefixWord, tailWord_1432833, baseEnd_1432833] using wordTrace_append hprefix tailTrace_1432833
  have hstable : (prefixWord ++ tailWord_1432833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432833).length < 2 ^ (prefixWord ++ tailWord_1432833).sum := by decide
  have hdescent : baseEnd_1432833 < baseStart_1432833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432846 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1432846 : Nat := 118140960795 + 1432846 * 2 ^ 59
def prefixEnd_1432846 : Nat := 4983230072969 + 3 ^ 40 * 1432846 * 2
def baseEnd_1432846 : Nat := 245246233957402072378489

theorem tailTrace_1432846 : CollatzResearch.WordTrace tailWord_1432846 prefixEnd_1432846 245246233957402072378489 := by
  unfold tailWord_1432846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532523370881390932437799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34840124644700751639668261 6532523370881390932437799)
  ·
    refine ⟨9798785056322086398656699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6532523370881390932437799 9798785056322086398656699)
    ·
      refine ⟨14698177584483129597985049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9798785056322086398656699 14698177584483129597985049)
      ·
        refine ⟨11023633188362347198488787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14698177584483129597985049 11023633188362347198488787)
        ·
          refine ⟨16535449782543520797733181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023633188362347198488787 16535449782543520797733181)
          ·
            refine ⟨6200793668453820299149943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16535449782543520797733181 6200793668453820299149943)
            ·
              refine ⟨9301190502680730448724915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200793668453820299149943 9301190502680730448724915)
              ·
                refine ⟨13951785754021095673087373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9301190502680730448724915 13951785754021095673087373)
                ·
                  refine ⟨5231919657757910877407765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13951785754021095673087373 5231919657757910877407765)
                  ·
                    refine ⟨245246233957402072378489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5231919657757910877407765 245246233957402072378489)
                    ·
                      rfl

theorem cell23_1432846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1432846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432846 prefixEnd_1432846 := by exact prefixLift 1432846
  have htrace : WordTrace (prefixWord ++ tailWord_1432846) baseStart_1432846 baseEnd_1432846 := by
    simpa [prefixWord, tailWord_1432846, baseEnd_1432846] using wordTrace_append hprefix tailTrace_1432846
  have hstable : (prefixWord ++ tailWord_1432846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432846).length < 2 ^ (prefixWord ++ tailWord_1432846).sum := by decide
  have hdescent : baseEnd_1432846 < baseStart_1432846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432883 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4]
def baseStart_1432883 : Nat := 118140960795 + 1432883 * 2 ^ 59
def prefixEnd_1432883 : Nat := 4983230072969 + 3 ^ 40 * 1432883 * 2
def baseEnd_1432883 : Nat := 735757700656422572372797

theorem tailTrace_1432883 : CollatzResearch.WordTrace tailWord_1432883 prefixEnd_1432883 735757700656422572372797 := by
  unfold tailWord_1432883
  simp only [CollatzResearch.WordTrace]
  refine ⟨52261536467917082778599303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34841024311944721852399535 52261536467917082778599303)
  ·
    refine ⟨78392304701875624167898955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52261536467917082778599303 78392304701875624167898955)
    ·
      refine ⟨117588457052813436251848433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78392304701875624167898955 117588457052813436251848433)
      ·
        refine ⟨88191342789610077188886325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117588457052813436251848433 88191342789610077188886325)
        ·
          refine ⟨8267938386525944736458093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88191342789610077188886325 8267938386525944736458093)
          ·
            refine ⟨3100476894947229276171785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8267938386525944736458093 3100476894947229276171785)
            ·
              refine ⟨2325357671210421957128839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100476894947229276171785 2325357671210421957128839)
              ·
                refine ⟨3488036506815632935693259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325357671210421957128839 3488036506815632935693259)
                ·
                  refine ⟨5232054760223449403539889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488036506815632935693259 5232054760223449403539889)
                  ·
                    refine ⟨3924041070167587052654917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232054760223449403539889 3924041070167587052654917)
                    ·
                      refine ⟨735757700656422572372797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3924041070167587052654917 735757700656422572372797)
                      ·
                        rfl

theorem cell23_1432883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_1432883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432883 prefixEnd_1432883 := by exact prefixLift 1432883
  have htrace : WordTrace (prefixWord ++ tailWord_1432883) baseStart_1432883 baseEnd_1432883 := by
    simpa [prefixWord, tailWord_1432883, baseEnd_1432883] using wordTrace_append hprefix tailTrace_1432883
  have hstable : (prefixWord ++ tailWord_1432883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432883).length < 2 ^ (prefixWord ++ tailWord_1432883).sum := by decide
  have hdescent : baseEnd_1432883 < baseStart_1432883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432900 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1432900 : Nat := 118140960795 + 1432900 * 2 ^ 59
def prefixEnd_1432900 : Nat := 4983230072969 + 3 ^ 40 * 1432900 * 2
def baseEnd_1432900 : Nat := 735766429827549005860219

theorem tailTrace_1432900 : CollatzResearch.WordTrace tailWord_1432900 prefixEnd_1432900 735766429827549005860219 := by
  unfold tailWord_1432900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131078254427747340984077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34841437672570329787978769 26131078254427747340984077)
  ·
    refine ⟨9799154345410405252869029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26131078254427747340984077 9799154345410405252869029)
    ·
      refine ⟨1837341439764450984912943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9799154345410405252869029 1837341439764450984912943)
      ·
        refine ⟨2756012159646676477369415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837341439764450984912943 2756012159646676477369415)
        ·
          refine ⟨4134018239470014716054123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756012159646676477369415 4134018239470014716054123)
          ·
            refine ⟨6201027359205022074081185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134018239470014716054123 6201027359205022074081185)
            ·
              refine ⟨4650770519403766555560889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201027359205022074081185 4650770519403766555560889)
              ·
                refine ⟨3488077889552824916670667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650770519403766555560889 3488077889552824916670667)
                ·
                  refine ⟨5232116834329237375006001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488077889552824916670667 5232116834329237375006001)
                  ·
                    refine ⟨3924087625746928031254501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232116834329237375006001 3924087625746928031254501)
                    ·
                      refine ⟨735766429827549005860219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3924087625746928031254501 735766429827549005860219)
                      ·
                        rfl

theorem cell23_1432900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1432900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432900 prefixEnd_1432900 := by exact prefixLift 1432900
  have htrace : WordTrace (prefixWord ++ tailWord_1432900) baseStart_1432900 baseEnd_1432900 := by
    simpa [prefixWord, tailWord_1432900, baseEnd_1432900] using wordTrace_append hprefix tailTrace_1432900
  have hstable : (prefixWord ++ tailWord_1432900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432900).length < 2 ^ (prefixWord ++ tailWord_1432900).sum := by decide
  have hdescent : baseEnd_1432900 < baseStart_1432900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432903 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1432903 : Nat := 118140960795 + 1432903 * 2 ^ 59
def prefixEnd_1432903 : Nat := 4983230072969 + 3 ^ 40 * 1432903 * 2
def baseEnd_1432903 : Nat := 735767970269512494122705

theorem tailTrace_1432903 : CollatzResearch.WordTrace tailWord_1432903 prefixEnd_1432903 735767970269512494122705 := by
  unfold tailWord_1432903
  simp only [CollatzResearch.WordTrace]
  refine ⟨52262265927844626194327363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34841510618563084129551575 52262265927844626194327363)
  ·
    refine ⟨78393398891766939291491045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52262265927844626194327363 78393398891766939291491045)
    ·
      refine ⟨14698762292206301117154571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78393398891766939291491045 14698762292206301117154571)
      ·
        refine ⟨22048143438309451675731857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14698762292206301117154571 22048143438309451675731857)
        ·
          refine ⟨16536107578732088756798893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22048143438309451675731857 16536107578732088756798893)
          ·
            refine ⟨6201040342024533283799585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16536107578732088756798893 6201040342024533283799585)
            ·
              refine ⟨4650780256518399962849689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201040342024533283799585 4650780256518399962849689)
              ·
                refine ⟨3488085192388799972137267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650780256518399962849689 3488085192388799972137267)
                ·
                  refine ⟨5232127788583199958205901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488085192388799972137267 5232127788583199958205901)
                  ·
                    refine ⟨1962047920718699984327213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5232127788583199958205901 1962047920718699984327213)
                    ·
                      refine ⟨735767970269512494122705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962047920718699984327213 735767970269512494122705)
                      ·
                        rfl

theorem cell23_1432903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1432903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432903 prefixEnd_1432903 := by exact prefixLift 1432903
  have htrace : WordTrace (prefixWord ++ tailWord_1432903) baseStart_1432903 baseEnd_1432903 := by
    simpa [prefixWord, tailWord_1432903, baseEnd_1432903] using wordTrace_append hprefix tailTrace_1432903
  have hstable : (prefixWord ++ tailWord_1432903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432903).length < 2 ^ (prefixWord ++ tailWord_1432903).sum := by decide
  have hdescent : baseEnd_1432903 < baseStart_1432903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432963 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1432963 : Nat := 118140960795 + 1432963 * 2 ^ 59
def prefixEnd_1432963 : Nat := 4983230072969 + 3 ^ 40 * 1432963 * 2
def baseEnd_1432963 : Nat := 735798779108782259372429

theorem tailTrace_1432963 : CollatzResearch.WordTrace tailWord_1432963 prefixEnd_1432963 735798779108782259372429 := by
  unfold tailWord_1432963
  simp only [CollatzResearch.WordTrace]
  refine ⟨52264454307627256441511543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34842969538418170961007695 52264454307627256441511543)
  ·
    refine ⟨78396681461440884662267315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52264454307627256441511543 78396681461440884662267315)
    ·
      refine ⟨117595022192161326993400973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78396681461440884662267315 117595022192161326993400973)
      ·
        refine ⟨44098133322060497622525365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117595022192161326993400973 44098133322060497622525365)
        ·
          refine ⟨4134199998943171652111753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44098133322060497622525365 4134199998943171652111753)
          ·
            refine ⟨3100649999207378739083815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4134199998943171652111753 3100649999207378739083815)
            ·
              refine ⟨4650974998811068108625723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100649999207378739083815 4650974998811068108625723)
              ·
                refine ⟨6976462498216602162938585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650974998811068108625723 6976462498216602162938585)
                ·
                  refine ⟨5232346873662451622203939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6976462498216602162938585 5232346873662451622203939)
                  ·
                    refine ⟨7848520310493677433305909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232346873662451622203939 7848520310493677433305909)
                    ·
                      refine ⟨735798779108782259372429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7848520310493677433305909 735798779108782259372429)
                      ·
                        rfl

theorem cell23_1432963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1432963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432963 prefixEnd_1432963 := by exact prefixLift 1432963
  have htrace : WordTrace (prefixWord ++ tailWord_1432963) baseStart_1432963 baseEnd_1432963 := by
    simpa [prefixWord, tailWord_1432963, baseEnd_1432963] using wordTrace_append hprefix tailTrace_1432963
  have hstable : (prefixWord ++ tailWord_1432963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432963).length < 2 ^ (prefixWord ++ tailWord_1432963).sum := by decide
  have hdescent : baseEnd_1432963 < baseStart_1432963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432988 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1432988 : Nat := 118140960795 + 1432988 * 2 ^ 59
def prefixEnd_1432988 : Nat := 4983230072969 + 3 ^ 40 * 1432988 * 2
def baseEnd_1432988 : Nat := 735811616125144661559815

theorem tailTrace_1432988 : CollatzResearch.WordTrace tailWord_1432988 prefixEnd_1432988 735811616125144661559815 := by
  unfold tailWord_1432988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26132683066268342855585809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34843577421691123807447745 26132683066268342855585809)
  ·
    refine ⟨19599512299701257141689357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26132683066268342855585809 19599512299701257141689357)
    ·
      refine ⟨7349817112387971428133509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19599512299701257141689357 7349817112387971428133509)
      ·
        refine ⟨1378090708572744642775033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7349817112387971428133509 1378090708572744642775033)
        ·
          refine ⟨1033568031429558482081275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378090708572744642775033 1033568031429558482081275)
          ·
            refine ⟨1550352047144337723121913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033568031429558482081275 1550352047144337723121913)
            ·
              refine ⟨1162764035358253292341435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550352047144337723121913 1162764035358253292341435)
              ·
                refine ⟨1744146053037379938512153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162764035358253292341435 1744146053037379938512153)
                ·
                  refine ⟨1308109539778034953884115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744146053037379938512153 1308109539778034953884115)
                  ·
                    refine ⟨1962164309667052430826173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1308109539778034953884115 1962164309667052430826173)
                    ·
                      refine ⟨735811616125144661559815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962164309667052430826173 735811616125144661559815)
                      ·
                        rfl

theorem cell23_1432988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1432988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432988 prefixEnd_1432988 := by exact prefixLift 1432988
  have htrace : WordTrace (prefixWord ++ tailWord_1432988) baseStart_1432988 baseEnd_1432988 := by
    simpa [prefixWord, tailWord_1432988, baseEnd_1432988] using wordTrace_append hprefix tailTrace_1432988
  have hstable : (prefixWord ++ tailWord_1432988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432988).length < 2 ^ (prefixWord ++ tailWord_1432988).sum := by decide
  have hdescent : baseEnd_1432988 < baseStart_1432988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432994 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1432994 : Nat := 118140960795 + 1432994 * 2 ^ 59
def prefixEnd_1432994 : Nat := 4983230072969 + 3 ^ 40 * 1432994 * 2
def baseEnd_1432994 : Nat := 735814697009071638084787

theorem tailTrace_1432994 : CollatzResearch.WordTrace tailWord_1432994 prefixEnd_1432994 735814697009071638084787 := by
  unfold tailWord_1432994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066396242628737183972509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34843723313676632490593357 13066396242628737183972509)
  ·
    refine ⟨4899898590985776443989691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13066396242628737183972509 4899898590985776443989691)
    ·
      refine ⟨7349847886478664665984537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899898590985776443989691 7349847886478664665984537)
      ·
        refine ⟨5512385914858998499488403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7349847886478664665984537 5512385914858998499488403)
        ·
          refine ⟨8268578872288497749232605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512385914858998499488403 8268578872288497749232605)
          ·
            refine ⟨3100717077108186655962227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8268578872288497749232605 3100717077108186655962227)
            ·
              refine ⟨4651075615662279983943341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100717077108186655962227 4651075615662279983943341)
              ·
                refine ⟨1744153355873354993978753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4651075615662279983943341 1744153355873354993978753)
                ·
                  refine ⟨1308115016905016245484065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744153355873354993978753 1308115016905016245484065)
                  ·
                    refine ⟨981086262678762184113049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1308115016905016245484065 981086262678762184113049)
                    ·
                      refine ⟨735814697009071638084787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981086262678762184113049 735814697009071638084787)
                      ·
                        rfl

theorem cell23_1432994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1432994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1432994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1432994 prefixEnd_1432994 := by exact prefixLift 1432994
  have htrace : WordTrace (prefixWord ++ tailWord_1432994) baseStart_1432994 baseEnd_1432994 := by
    simpa [prefixWord, tailWord_1432994, baseEnd_1432994] using wordTrace_append hprefix tailTrace_1432994
  have hstable : (prefixWord ++ tailWord_1432994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432994).length < 2 ^ (prefixWord ++ tailWord_1432994).sum := by decide
  have hdescent : baseEnd_1432994 < baseStart_1432994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433050 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_1433050 : Nat := 118140960795 + 1433050 * 2 ^ 59
def prefixEnd_1433050 : Nat := 4983230072969 + 3 ^ 40 * 1433050 * 2
def baseEnd_1433050 : Nat := 735843451925723418984529

theorem tailTrace_1433050 : CollatzResearch.WordTrace tailWord_1433050 prefixEnd_1433050 735843451925723418984529 := by
  unfold tailWord_1433050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066906864578017574982151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34845084972208046866619069 13066906864578017574982151)
  ·
    refine ⟨19600360296867026362473227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066906864578017574982151 19600360296867026362473227)
    ·
      refine ⟨29400540445300539543709841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19600360296867026362473227 29400540445300539543709841)
      ·
        refine ⟨22050405333975404657782381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29400540445300539543709841 22050405333975404657782381)
        ·
          refine ⟨8268902000240776746668393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22050405333975404657782381 8268902000240776746668393)
          ·
            refine ⟨6201676500180582560001295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8268902000240776746668393 6201676500180582560001295)
            ·
              refine ⟨9302514750270873840001943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201676500180582560001295 9302514750270873840001943)
              ·
                refine ⟨13953772125406310760002915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9302514750270873840001943 13953772125406310760002915)
                ·
                  refine ⟨20930658188109466140004373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13953772125406310760002915 20930658188109466140004373)
                  ·
                    refine ⟨981124602567631225312705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20930658188109466140004373 981124602567631225312705)
                    ·
                      refine ⟨735843451925723418984529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981124602567631225312705 735843451925723418984529)
                      ·
                        rfl

theorem cell23_1433050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_1433050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433050 prefixEnd_1433050 := by exact prefixLift 1433050
  have htrace : WordTrace (prefixWord ++ tailWord_1433050) baseStart_1433050 baseEnd_1433050 := by
    simpa [prefixWord, tailWord_1433050, baseEnd_1433050] using wordTrace_append hprefix tailTrace_1433050
  have hstable : (prefixWord ++ tailWord_1433050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433050).length < 2 ^ (prefixWord ++ tailWord_1433050).sum := by decide
  have hdescent : baseEnd_1433050 < baseStart_1433050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433070 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1433070 : Nat := 118140960795 + 1433070 * 2 ^ 59
def prefixEnd_1433070 : Nat := 4983230072969 + 3 ^ 40 * 1433070 * 2
def baseEnd_1433070 : Nat := 735853721538813340734437

theorem tailTrace_1433070 : CollatzResearch.WordTrace tailWord_1433070 prefixEnd_1433070 735853721538813340734437 := by
  unfold tailWord_1433070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533544614779951714457083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34845571278826409143771109 6533544614779951714457083)
  ·
    refine ⟨9800316922169927571685625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6533544614779951714457083 9800316922169927571685625)
    ·
      refine ⟨7350237691627445678764219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9800316922169927571685625 7350237691627445678764219)
      ·
        refine ⟨11025356537441168518146329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350237691627445678764219 11025356537441168518146329)
        ·
          refine ⟨8269017403080876388609747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11025356537441168518146329 8269017403080876388609747)
          ·
            refine ⟨12403526104621314582914621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269017403080876388609747 12403526104621314582914621)
            ·
              refine ⟨4651322289232992968592983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12403526104621314582914621 4651322289232992968592983)
              ·
                refine ⟨6976983433849489452889475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651322289232992968592983 6976983433849489452889475)
                ·
                  refine ⟨10465475150774234179334213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976983433849489452889475 10465475150774234179334213)
                  ·
                    refine ⟨1962276590770168908625165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10465475150774234179334213 1962276590770168908625165)
                    ·
                      refine ⟨735853721538813340734437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962276590770168908625165 735853721538813340734437)
                      ·
                        rfl

theorem cell23_1433070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1433070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433070 prefixEnd_1433070 := by exact prefixLift 1433070
  have htrace : WordTrace (prefixWord ++ tailWord_1433070) baseStart_1433070 baseEnd_1433070 := by
    simpa [prefixWord, tailWord_1433070, baseEnd_1433070] using wordTrace_append hprefix tailTrace_1433070
  have hstable : (prefixWord ++ tailWord_1433070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433070).length < 2 ^ (prefixWord ++ tailWord_1433070).sum := by decide
  have hdescent : baseEnd_1433070 < baseStart_1433070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433117 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1433117 : Nat := 118140960795 + 1433117 * 2 ^ 59
def prefixEnd_1433117 : Nat := 4983230072969 + 3 ^ 40 * 1433117 * 2
def baseEnd_1433117 : Nat := 735877855129574656846721

theorem tailTrace_1433117 : CollatzResearch.WordTrace tailWord_1433117 prefixEnd_1433117 735877855129574656846721 := by
  unfold tailWord_1433117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52270071149069340742617605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34846714099379560495078403 52270071149069340742617605)
  ·
    refine ⟨9800638340450501389240801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52270071149069340742617605 9800638340450501389240801)
    ·
      refine ⟨7350478755337876041930601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9800638340450501389240801 7350478755337876041930601)
      ·
        refine ⟨5512859066503407031447951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7350478755337876041930601 5512859066503407031447951)
        ·
          refine ⟨8269288599755110547171927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512859066503407031447951 8269288599755110547171927)
          ·
            refine ⟨12403932899632665820757891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269288599755110547171927 12403932899632665820757891)
            ·
              refine ⟨18605899349448998731136837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12403932899632665820757891 18605899349448998731136837)
              ·
                refine ⟨3488606128021687262088157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18605899349448998731136837 3488606128021687262088157)
                ·
                  refine ⟨1308227298008132723283059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3488606128021687262088157 1308227298008132723283059)
                  ·
                    refine ⟨1962340947012199084924589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1308227298008132723283059 1962340947012199084924589)
                    ·
                      refine ⟨735877855129574656846721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962340947012199084924589 735877855129574656846721)
                      ·
                        rfl

theorem cell23_1433117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1433117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433117 prefixEnd_1433117 := by exact prefixLift 1433117
  have htrace : WordTrace (prefixWord ++ tailWord_1433117) baseStart_1433117 baseEnd_1433117 := by
    simpa [prefixWord, tailWord_1433117, baseEnd_1433117] using wordTrace_append hprefix tailTrace_1433117
  have hstable : (prefixWord ++ tailWord_1433117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433117).length < 2 ^ (prefixWord ++ tailWord_1433117).sum := by decide
  have hdescent : baseEnd_1433117 < baseStart_1433117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433128 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1433128 : Nat := 118140960795 + 1433128 * 2 ^ 59
def prefixEnd_1433128 : Nat := 4983230072969 + 3 ^ 40 * 1433128 * 2
def baseEnd_1433128 : Nat := 245294501138924704603057

theorem tailTrace_1433128 : CollatzResearch.WordTrace tailWord_1433128 prefixEnd_1433128 245294501138924704603057 := by
  unfold tailWord_1433128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26135236176014744810634019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34846981568019659747512025 26135236176014744810634019)
  ·
    refine ⟨39202854264022117215951029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26135236176014744810634019 39202854264022117215951029)
    ·
      refine ⟨3675267587252073488995409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39202854264022117215951029 3675267587252073488995409)
      ·
        refine ⟨2756450690439055116746557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3675267587252073488995409 2756450690439055116746557)
        ·
          refine ⟨1033669008914645668779959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2756450690439055116746557 1033669008914645668779959)
          ·
            refine ⟨1550503513371968503169939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033669008914645668779959 1550503513371968503169939)
            ·
              refine ⟨2325755270057952754754909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550503513371968503169939 2325755270057952754754909)
              ·
                refine ⟨872158226271732283033091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2325755270057952754754909 872158226271732283033091)
                ·
                  refine ⟨1308237339407598424549637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872158226271732283033091 1308237339407598424549637)
                  ·
                    refine ⟨245294501138924704603057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308237339407598424549637 245294501138924704603057)
                    ·
                      rfl

theorem cell23_1433128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1433128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433128 prefixEnd_1433128 := by exact prefixLift 1433128
  have htrace : WordTrace (prefixWord ++ tailWord_1433128) baseStart_1433128 baseEnd_1433128 := by
    simpa [prefixWord, tailWord_1433128, baseEnd_1433128] using wordTrace_append hprefix tailTrace_1433128
  have hstable : (prefixWord ++ tailWord_1433128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433128).length < 2 ^ (prefixWord ++ tailWord_1433128).sum := by decide
  have hdescent : baseEnd_1433128 < baseStart_1433128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433151 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 1, 1, 3]
def baseStart_1433151 : Nat := 118140960795 + 1433151 * 2 ^ 59
def prefixEnd_1433151 : Nat := 4983230072969 + 3 ^ 40 * 1433151 * 2
def baseEnd_1433151 : Nat := 735895313471827523821565

theorem tailTrace_1433151 : CollatzResearch.WordTrace tailWord_1433151 prefixEnd_1433151 735895313471827523821565 := by
  unfold tailWord_1433151
  simp only [CollatzResearch.WordTrace]
  refine ⟨52271311230946164549355307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34847540820630776366236871 52271311230946164549355307)
  ·
    refine ⟨78406966846419246824032961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52271311230946164549355307 78406966846419246824032961)
    ·
      refine ⟨58805225134814435118024721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78406966846419246824032961 58805225134814435118024721)
      ·
        refine ⟨44103918851110826338518541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58805225134814435118024721 44103918851110826338518541)
        ·
          refine ⟨16538969569166559876944453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44103918851110826338518541 16538969569166559876944453)
          ·
            refine ⟨3101056794218729976927085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16538969569166559876944453 3101056794218729976927085)
            ·
              refine ⟨1162896297832023741347657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3101056794218729976927085 1162896297832023741347657)
              ·
                refine ⟨872172223374017806010743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162896297832023741347657 872172223374017806010743)
                ·
                  refine ⟨1308258335061026709016115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872172223374017806010743 1308258335061026709016115)
                  ·
                    refine ⟨1962387502591540063524173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1308258335061026709016115 1962387502591540063524173)
                    ·
                      refine ⟨735895313471827523821565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962387502591540063524173 735895313471827523821565)
                      ·
                        rfl

theorem cell23_1433151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_1433151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433151 prefixEnd_1433151 := by exact prefixLift 1433151
  have htrace : WordTrace (prefixWord ++ tailWord_1433151) baseStart_1433151 baseEnd_1433151 := by
    simpa [prefixWord, tailWord_1433151, baseEnd_1433151] using wordTrace_append hprefix tailTrace_1433151
  have hstable : (prefixWord ++ tailWord_1433151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433151).length < 2 ^ (prefixWord ++ tailWord_1433151).sum := by decide
  have hdescent : baseEnd_1433151 < baseStart_1433151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433158 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1433158 : Nat := 118140960795 + 1433158 * 2 ^ 59
def prefixEnd_1433158 : Nat := 4983230072969 + 3 ^ 40 * 1433158 * 2
def baseEnd_1433158 : Nat := 81766545315156555159337

theorem tailTrace_1433158 : CollatzResearch.WordTrace tailWord_1433158 prefixEnd_1433158 81766545315156555159337 := by
  unfold tailWord_1433158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633486454435025148276879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34847711027947203163240085 1633486454435025148276879)
  ·
    refine ⟨2450229681652537722415319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633486454435025148276879 2450229681652537722415319)
    ·
      refine ⟨3675344522478806583622979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450229681652537722415319 3675344522478806583622979)
      ·
        refine ⟨5513016783718209875434469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675344522478806583622979 5513016783718209875434469)
        ·
          refine ⟨1033690646947164351643963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5513016783718209875434469 1033690646947164351643963)
          ·
            refine ⟨1550535970420746527465945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033690646947164351643963 1550535970420746527465945)
            ·
              refine ⟨1162901977815559895599459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550535970420746527465945 1162901977815559895599459)
              ·
                refine ⟨1744352966723339843399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162901977815559895599459 1744352966723339843399189)
                ·
                  refine ⟨81766545315156555159337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1744352966723339843399189 81766545315156555159337)
                  ·
                    rfl

theorem cell23_1433158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1433158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433158 prefixEnd_1433158 := by exact prefixLift 1433158
  have htrace : WordTrace (prefixWord ++ tailWord_1433158) baseStart_1433158 baseEnd_1433158 := by
    simpa [prefixWord, tailWord_1433158, baseEnd_1433158] using wordTrace_append hprefix tailTrace_1433158
  have hstable : (prefixWord ++ tailWord_1433158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433158).length < 2 ^ (prefixWord ++ tailWord_1433158).sum := by decide
  have hdescent : baseEnd_1433158 < baseStart_1433158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433170 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1433170 : Nat := 118140960795 + 1433170 * 2 ^ 59
def prefixEnd_1433170 : Nat := 4983230072969 + 3 ^ 40 * 1433170 * 2
def baseEnd_1433170 : Nat := 735905069604262949483977

theorem tailTrace_1433170 : CollatzResearch.WordTrace tailWord_1433170 prefixEnd_1433170 735905069604262949483977 := by
  unfold tailWord_1433170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068001054469332698574241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34848002811918220529531309 13068001054469332698574241)
  ·
    refine ⟨9801000790851999523930681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13068001054469332698574241 9801000790851999523930681)
    ·
      refine ⟨7350750593138999642948011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9801000790851999523930681 7350750593138999642948011)
      ·
        refine ⟨11026125889708499464422017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350750593138999642948011 11026125889708499464422017)
        ·
          refine ⟨8269594417281374598316513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11026125889708499464422017 8269594417281374598316513)
          ·
            refine ⟨6202195812961030948737385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8269594417281374598316513 6202195812961030948737385)
            ·
              refine ⟨4651646859720773211553039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6202195812961030948737385 4651646859720773211553039)
              ·
                refine ⟨6977470289581159817329559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651646859720773211553039 6977470289581159817329559)
                ·
                  refine ⟨10466205434371739725994339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977470289581159817329559 10466205434371739725994339)
                  ·
                    refine ⟨15699308151557609588991509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10466205434371739725994339 15699308151557609588991509)
                    ·
                      refine ⟨735905069604262949483977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15699308151557609588991509 735905069604262949483977)
                      ·
                        rfl

theorem cell23_1433170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1433170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433170 prefixEnd_1433170 := by exact prefixLift 1433170
  have htrace : WordTrace (prefixWord ++ tailWord_1433170) baseStart_1433170 baseEnd_1433170 := by
    simpa [prefixWord, tailWord_1433170, baseEnd_1433170] using wordTrace_append hprefix tailTrace_1433170
  have hstable : (prefixWord ++ tailWord_1433170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433170).length < 2 ^ (prefixWord ++ tailWord_1433170).sum := by decide
  have hdescent : baseEnd_1433170 < baseStart_1433170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433180 : List Nat := [2, 2, 4, 1, 2, 1, 2, 9]
def baseStart_1433180 : Nat := 118140960795 + 1433180 * 2 ^ 59
def prefixEnd_1433180 : Nat := 4983230072969 + 3 ^ 40 * 1433180 * 2
def baseEnd_1433180 : Nat := 27255933496696589272553

theorem tailTrace_1433180 : CollatzResearch.WordTrace tailWord_1433180 prefixEnd_1433180 27255933496696589272553 := by
  unfold tailWord_1433180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136184473920551251080497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34848245965227401668107329 26136184473920551251080497)
  ·
    refine ⟨19602138355440413438310373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26136184473920551251080497 19602138355440413438310373)
    ·
      refine ⟨3675400941645077519683195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19602138355440413438310373 3675400941645077519683195)
      ·
        refine ⟨5513101412467616279524793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675400941645077519683195 5513101412467616279524793)
        ·
          refine ⟨4134826059350712209643595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5513101412467616279524793 4134826059350712209643595)
          ·
            refine ⟨6202239089026068314465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134826059350712209643595 6202239089026068314465393)
            ·
              refine ⟨4651679316769551235849045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6202239089026068314465393 4651679316769551235849045)
              ·
                refine ⟨27255933496696589272553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4651679316769551235849045 27255933496696589272553)
                ·
                  rfl

theorem cell23_1433180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 9].length) (baseStart_1433180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433180 prefixEnd_1433180 := by exact prefixLift 1433180
  have htrace : WordTrace (prefixWord ++ tailWord_1433180) baseStart_1433180 baseEnd_1433180 := by
    simpa [prefixWord, tailWord_1433180, baseEnd_1433180] using wordTrace_append hprefix tailTrace_1433180
  have hstable : (prefixWord ++ tailWord_1433180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433180).length < 2 ^ (prefixWord ++ tailWord_1433180).sum := by decide
  have hdescent : baseEnd_1433180 < baseStart_1433180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433203 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_1433203 : Nat := 118140960795 + 1433203 * 2 ^ 59
def prefixEnd_1433203 : Nat := 4983230072969 + 3 ^ 40 * 1433203 * 2
def baseEnd_1433203 : Nat := 735922014465861320371325

theorem tailTrace_1433203 : CollatzResearch.WordTrace tailWord_1433203 prefixEnd_1433203 735922014465861320371325 := by
  unfold tailWord_1433203
  simp only [CollatzResearch.WordTrace]
  refine ⟨52273207826757777430248263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34848805217838518286832175 52273207826757777430248263)
  ·
    refine ⟨78409811740136666145372395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52273207826757777430248263 78409811740136666145372395)
    ·
      refine ⟨117614717610204999218058593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78409811740136666145372395 117614717610204999218058593)
      ·
        refine ⟨88211038207653749413543945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117614717610204999218058593 88211038207653749413543945)
        ·
          refine ⟨66158278655740312060157959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88211038207653749413543945 66158278655740312060157959)
          ·
            refine ⟨99237417983610468090236939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66158278655740312060157959 99237417983610468090236939)
            ·
              refine ⟨148856126975415702135355409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99237417983610468090236939 148856126975415702135355409)
              ·
                refine ⟨111642095231561776601516557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148856126975415702135355409 111642095231561776601516557)
                ·
                  refine ⟨41865785711835666225568709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111642095231561776601516557 41865785711835666225568709)
                  ·
                    refine ⟨7849834820969187417294133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41865785711835666225568709 7849834820969187417294133)
                    ·
                      refine ⟨735922014465861320371325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7849834820969187417294133 735922014465861320371325)
                      ·
                        rfl

theorem cell23_1433203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_1433203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433203 prefixEnd_1433203 := by exact prefixLift 1433203
  have htrace : WordTrace (prefixWord ++ tailWord_1433203) baseStart_1433203 baseEnd_1433203 := by
    simpa [prefixWord, tailWord_1433203, baseEnd_1433203] using wordTrace_append hprefix tailTrace_1433203
  have hstable : (prefixWord ++ tailWord_1433203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433203).length < 2 ^ (prefixWord ++ tailWord_1433203).sum := by decide
  have hdescent : baseEnd_1433203 < baseStart_1433203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433243 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_1433243 : Nat := 118140960795 + 1433243 * 2 ^ 59
def prefixEnd_1433243 : Nat := 4983230072969 + 3 ^ 40 * 1433243 * 2
def baseEnd_1433243 : Nat := 735942553692041163871141

theorem tailTrace_1433243 : CollatzResearch.WordTrace tailWord_1433243 prefixEnd_1433243 735942553692041163871141 := by
  unfold tailWord_1433243
  simp only [CollatzResearch.WordTrace]
  refine ⟨52274666746612864261704383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34849777831075242841136255 52274666746612864261704383)
  ·
    refine ⟨78412000119919296392556575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52274666746612864261704383 78412000119919296392556575)
    ·
      refine ⟨117618000179878944588834863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78412000119919296392556575 117618000179878944588834863)
      ·
        refine ⟨176427000269818416883252295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117618000179878944588834863 176427000269818416883252295)
        ·
          refine ⟨264640500404727625324878443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176427000269818416883252295 264640500404727625324878443)
          ·
            refine ⟨396960750607091437987317665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264640500404727625324878443 396960750607091437987317665)
            ·
              refine ⟨297720562955318578490488249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396960750607091437987317665 297720562955318578490488249)
              ·
                refine ⟨223290422216488933867866187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297720562955318578490488249 223290422216488933867866187)
                ·
                  refine ⟨334935633324733400801799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223290422216488933867866187 334935633324733400801799281)
                  ·
                    refine ⟨251201724993550050601349461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334935633324733400801799281 251201724993550050601349461)
                    ·
                      refine ⟨735942553692041163871141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 251201724993550050601349461 735942553692041163871141)
                      ·
                        rfl

theorem cell23_1433243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_1433243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433243 prefixEnd_1433243 := by exact prefixLift 1433243
  have htrace : WordTrace (prefixWord ++ tailWord_1433243) baseStart_1433243 baseEnd_1433243 := by
    simpa [prefixWord, tailWord_1433243, baseEnd_1433243] using wordTrace_append hprefix tailTrace_1433243
  have hstable : (prefixWord ++ tailWord_1433243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433243).length < 2 ^ (prefixWord ++ tailWord_1433243).sum := by decide
  have hdescent : baseEnd_1433243 < baseStart_1433243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433317 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_1433317 : Nat := 118140960795 + 1433317 * 2 ^ 59
def prefixEnd_1433317 : Nat := 4983230072969 + 3 ^ 40 * 1433317 * 2
def baseEnd_1433317 : Nat := 245326850420157958115267

theorem tailTrace_1433317 : CollatzResearch.WordTrace tailWord_1433317 prefixEnd_1433317 245326850420157958115267 := by
  unfold tailWord_1433317
  simp only [CollatzResearch.WordTrace]
  refine ⟨52277365748344774899898205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34851577165563183266598803 52277365748344774899898205)
  ·
    refine ⟨19604012155629290587461827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52277365748344774899898205 19604012155629290587461827)
    ·
      refine ⟨29406018233443935881192741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19604012155629290587461827 29406018233443935881192741)
      ·
        refine ⟨5513628418770737977723639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29406018233443935881192741 5513628418770737977723639)
        ·
          refine ⟨8270442628156106966585459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513628418770737977723639 8270442628156106966585459)
          ·
            refine ⟨12405663942234160449878189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270442628156106966585459 12405663942234160449878189)
            ·
              refine ⟨4652123978337810168704321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12405663942234160449878189 4652123978337810168704321)
              ·
                refine ⟨3489092983753357626528241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652123978337810168704321 3489092983753357626528241)
                ·
                  refine ⟨2616819737815018219896181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489092983753357626528241 2616819737815018219896181)
                  ·
                    refine ⟨245326850420157958115267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2616819737815018219896181 245326850420157958115267)
                    ·
                      rfl

theorem cell23_1433317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_1433317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433317 prefixEnd_1433317 := by exact prefixLift 1433317
  have htrace : WordTrace (prefixWord ++ tailWord_1433317) baseStart_1433317 baseEnd_1433317 := by
    simpa [prefixWord, tailWord_1433317, baseEnd_1433317] using wordTrace_append hprefix tailTrace_1433317
  have hstable : (prefixWord ++ tailWord_1433317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433317).length < 2 ^ (prefixWord ++ tailWord_1433317).sum := by decide
  have hdescent : baseEnd_1433317 < baseStart_1433317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433332 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1433332 : Nat := 118140960795 + 1433332 * 2 ^ 59
def prefixEnd_1433332 : Nat := 4983230072969 + 3 ^ 40 * 1433332 * 2
def baseEnd_1433332 : Nat := 735988253470291315658233

theorem tailTrace_1433332 : CollatzResearch.WordTrace tailWord_1433332 prefixEnd_1433332 735988253470291315658233 := by
  unfold tailWord_1433332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26138956421645216230847125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34851941895526954974462833 26138956421645216230847125)
  ·
    refine ⟨1225263582264619510820959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26138956421645216230847125 1225263582264619510820959)
    ·
      refine ⟨1837895373396929266231439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1225263582264619510820959 1837895373396929266231439)
      ·
        refine ⟨2756843060095393899347159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837895373396929266231439 2756843060095393899347159)
        ·
          refine ⟨4135264590143090849020739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756843060095393899347159 4135264590143090849020739)
          ·
            refine ⟨6202896885214636273531109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135264590143090849020739 6202896885214636273531109)
            ·
              refine ⟨1163043165977744301287083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6202896885214636273531109 1163043165977744301287083)
              ·
                refine ⟨1744564748966616451930625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163043165977744301287083 1744564748966616451930625)
                ·
                  refine ⟨1308423561724962338947969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744564748966616451930625 1308423561724962338947969)
                  ·
                    refine ⟨981317671293721754210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1308423561724962338947969 981317671293721754210977)
                    ·
                      refine ⟨735988253470291315658233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981317671293721754210977 735988253470291315658233)
                      ·
                        rfl

theorem cell23_1433332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1433332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433332 prefixEnd_1433332 := by exact prefixLift 1433332
  have htrace : WordTrace (prefixWord ++ tailWord_1433332) baseStart_1433332 baseEnd_1433332 := by
    simpa [prefixWord, tailWord_1433332, baseEnd_1433332] using wordTrace_append hprefix tailTrace_1433332
  have hstable : (prefixWord ++ tailWord_1433332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433332).length < 2 ^ (prefixWord ++ tailWord_1433332).sum := by decide
  have hdescent : baseEnd_1433332 < baseStart_1433332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433347 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 3, 4]
def baseStart_1433347 : Nat := 118140960795 + 1433347 * 2 ^ 59
def prefixEnd_1433347 : Nat := 4983230072969 + 3 ^ 40 * 1433347 * 2
def baseEnd_1433347 : Nat := 245331985226702918990221

theorem tailTrace_1433347 : CollatzResearch.WordTrace tailWord_1433347 prefixEnd_1433347 245331985226702918990221 := by
  unfold tailWord_1433347
  simp only [CollatzResearch.WordTrace]
  refine ⟨52278459938236090023490295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34852306625490726682326863 52278459938236090023490295)
  ·
    refine ⟨78417689907354135035235443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52278459938236090023490295 78417689907354135035235443)
    ·
      refine ⟨117626534861031202552853165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78417689907354135035235443 117626534861031202552853165)
      ·
        refine ⟨44109950572886700957319937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117626534861031202552853165 44109950572886700957319937)
        ·
          refine ⟨33082462929665025717989953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44109950572886700957319937 33082462929665025717989953)
          ·
            refine ⟨24811847197248769288492465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33082462929665025717989953 24811847197248769288492465)
            ·
              refine ⟨18608885397936576966369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24811847197248769288492465 18608885397936576966369349)
              ·
                refine ⟨3489166012113108181194253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18608885397936576966369349 3489166012113108181194253)
                ·
                  refine ⟨1308437254542415567947845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3489166012113108181194253 1308437254542415567947845)
                  ·
                    refine ⟨245331985226702918990221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308437254542415567947845 245331985226702918990221)
                    ·
                      rfl

theorem cell23_1433347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 4].length) (baseStart_1433347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433347 prefixEnd_1433347 := by exact prefixLift 1433347
  have htrace : WordTrace (prefixWord ++ tailWord_1433347) baseStart_1433347 baseEnd_1433347 := by
    simpa [prefixWord, tailWord_1433347, baseEnd_1433347] using wordTrace_append hprefix tailTrace_1433347
  have hstable : (prefixWord ++ tailWord_1433347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433347).length < 2 ^ (prefixWord ++ tailWord_1433347).sum := by decide
  have hdescent : baseEnd_1433347 < baseStart_1433347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433354 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1433354 : Nat := 118140960795 + 1433354 * 2 ^ 59
def prefixEnd_1433354 : Nat := 4983230072969 + 3 ^ 40 * 1433354 * 2
def baseEnd_1433354 : Nat := 735999550044690229583131

theorem tailTrace_1433354 : CollatzResearch.WordTrace tailWord_1433354 prefixEnd_1433354 735999550044690229583131 := by
  unfold tailWord_1433354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069678812302682554748779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34852476832807153479330077 13069678812302682554748779)
  ·
    refine ⟨19604518218454023832123169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13069678812302682554748779 19604518218454023832123169)
    ·
      refine ⟨14703388663840517874092377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19604518218454023832123169 14703388663840517874092377)
      ·
        refine ⟨11027541497880388405569283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14703388663840517874092377 11027541497880388405569283)
        ·
          refine ⟨16541312246820582608353925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027541497880388405569283 16541312246820582608353925)
          ·
            refine ⟨3101496046278859239066361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16541312246820582608353925 3101496046278859239066361)
            ·
              refine ⟨2326122034709144429299771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101496046278859239066361 2326122034709144429299771)
              ·
                refine ⟨3489183052063716643949657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326122034709144429299771 3489183052063716643949657)
                ·
                  refine ⟨2616887289047787482962243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489183052063716643949657 2616887289047787482962243)
                  ·
                    refine ⟨3925330933571681224443365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616887289047787482962243 3925330933571681224443365)
                    ·
                      refine ⟨735999550044690229583131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3925330933571681224443365 735999550044690229583131)
                      ·
                        rfl

theorem cell23_1433354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1433354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433354 prefixEnd_1433354 := by exact prefixLift 1433354
  have htrace : WordTrace (prefixWord ++ tailWord_1433354) baseStart_1433354 baseEnd_1433354 := by
    simpa [prefixWord, tailWord_1433354, baseEnd_1433354] using wordTrace_append hprefix tailTrace_1433354
  have hstable : (prefixWord ++ tailWord_1433354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433354).length < 2 ^ (prefixWord ++ tailWord_1433354).sum := by decide
  have hdescent : baseEnd_1433354 < baseStart_1433354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433377 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 6]
def baseStart_1433377 : Nat := 118140960795 + 1433377 * 2 ^ 59
def prefixEnd_1433377 : Nat := 4983230072969 + 3 ^ 40 * 1433377 * 2
def baseEnd_1433377 : Nat := 81779040011082626621725

theorem tailTrace_1433377 : CollatzResearch.WordTrace tailWord_1433377 prefixEnd_1433377 81779040011082626621725 := by
  unfold tailWord_1433377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279554128127405147082385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34853036085418270098054923 52279554128127405147082385)
  ·
    refine ⟨39209665596095553860311789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52279554128127405147082385 39209665596095553860311789)
    ·
      refine ⟨14703624598535832697616921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39209665596095553860311789 14703624598535832697616921)
      ·
        refine ⟨11027718448901874523212691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14703624598535832697616921 11027718448901874523212691)
        ·
          refine ⟨16541577673352811784819037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027718448901874523212691 16541577673352811784819037)
          ·
            refine ⟨6203091627507304419307139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16541577673352811784819037 6203091627507304419307139)
            ·
              refine ⟨9304637441260956628960709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203091627507304419307139 9304637441260956628960709)
              ·
                refine ⟨1744619520236429367930133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9304637441260956628960709 1744619520236429367930133)
                ·
                  refine ⟨81779040011082626621725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1744619520236429367930133 81779040011082626621725)
                  ·
                    rfl

theorem cell23_1433377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_1433377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433377 prefixEnd_1433377 := by exact prefixLift 1433377
  have htrace : WordTrace (prefixWord ++ tailWord_1433377) baseStart_1433377 baseEnd_1433377 := by
    simpa [prefixWord, tailWord_1433377, baseEnd_1433377] using wordTrace_append hprefix tailTrace_1433377
  have hstable : (prefixWord ++ tailWord_1433377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433377).length < 2 ^ (prefixWord ++ tailWord_1433377).sum := by decide
  have hdescent : baseEnd_1433377 < baseStart_1433377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433381 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1433381 : Nat := 118140960795 + 1433381 * 2 ^ 59
def prefixEnd_1433381 : Nat := 4983230072969 + 3 ^ 40 * 1433381 * 2
def baseEnd_1433381 : Nat := 245337804674120541315169

theorem tailTrace_1433381 : CollatzResearch.WordTrace tailWord_1433381 prefixEnd_1433381 245337804674120541315169 := by
  unfold tailWord_1433381
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279700020112913830227997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34853133346741942553485331 52279700020112913830227997)
  ·
    refine ⟨19604887507542342686335499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52279700020112913830227997 19604887507542342686335499)
    ·
      refine ⟨29407331261313514029503249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19604887507542342686335499 29407331261313514029503249)
      ·
        refine ⟨22055498445985135522127437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29407331261313514029503249 22055498445985135522127437)
        ·
          refine ⟨8270811917244425820797789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22055498445985135522127437 8270811917244425820797789)
          ·
            refine ⟨3101554468966659682799171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8270811917244425820797789 3101554468966659682799171)
            ·
              refine ⟨4652331703449989524198757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101554468966659682799171 4652331703449989524198757)
              ·
                refine ⟨872312194396873035787267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4652331703449989524198757 872312194396873035787267)
                ·
                  refine ⟨1308468291595309553680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872312194396873035787267 1308468291595309553680901)
                  ·
                    refine ⟨245337804674120541315169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308468291595309553680901 245337804674120541315169)
                    ·
                      rfl

theorem cell23_1433381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1433381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433381 prefixEnd_1433381 := by exact prefixLift 1433381
  have htrace : WordTrace (prefixWord ++ tailWord_1433381) baseStart_1433381 baseEnd_1433381 := by
    simpa [prefixWord, tailWord_1433381, baseEnd_1433381] using wordTrace_append hprefix tailTrace_1433381
  have hstable : (prefixWord ++ tailWord_1433381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433381).length < 2 ^ (prefixWord ++ tailWord_1433381).sum := by decide
  have hdescent : baseEnd_1433381 < baseStart_1433381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433404 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_1433404 : Nat := 118140960795 + 1433404 * 2 ^ 59
def prefixEnd_1433404 : Nat := 4983230072969 + 3 ^ 40 * 1433404 * 2
def baseEnd_1433404 : Nat := 736025224077415033957901

theorem tailTrace_1433404 : CollatzResearch.WordTrace tailWord_1433404 prefixEnd_1433404 736025224077415033957901 := by
  unfold tailWord_1433404
  simp only [CollatzResearch.WordTrace]
  refine ⟨26140269449514794379157633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34853692599353059172210177 26140269449514794379157633)
  ·
    refine ⟨19605202087136095784368225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26140269449514794379157633 19605202087136095784368225)
    ·
      refine ⟨14703901565352071838276169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19605202087136095784368225 14703901565352071838276169)
      ·
        refine ⟨11027926174014053878707127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14703901565352071838276169 11027926174014053878707127)
        ·
          refine ⟨16541889261021080818060691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027926174014053878707127 16541889261021080818060691)
          ·
            refine ⟨24812833891531621227091037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16541889261021080818060691 24812833891531621227091037)
            ·
              refine ⟨9304812709324357960159139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24812833891531621227091037 9304812709324357960159139)
              ·
                refine ⟨13957219063986536940238709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304812709324357960159139 13957219063986536940238709)
                ·
                  refine ⟨1308489287248737838147379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13957219063986536940238709 1308489287248737838147379)
                  ·
                    refine ⟨1962733930873106757221069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1308489287248737838147379 1962733930873106757221069)
                    ·
                      refine ⟨736025224077415033957901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1962733930873106757221069 736025224077415033957901)
                      ·
                        rfl

theorem cell23_1433404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_1433404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433404 prefixEnd_1433404 := by exact prefixLift 1433404
  have htrace : WordTrace (prefixWord ++ tailWord_1433404) baseStart_1433404 baseEnd_1433404 := by
    simpa [prefixWord, tailWord_1433404, baseEnd_1433404] using wordTrace_append hprefix tailTrace_1433404
  have hstable : (prefixWord ++ tailWord_1433404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433404).length < 2 ^ (prefixWord ++ tailWord_1433404).sum := by decide
  have hdescent : baseEnd_1433404 < baseStart_1433404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433457 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1433457 : Nat := 118140960795 + 1433457 * 2 ^ 59
def prefixEnd_1433457 : Nat := 4983230072969 + 3 ^ 40 * 1433457 * 2
def baseEnd_1433457 : Nat := 736052438552103326595157

theorem tailTrace_1433457 : CollatzResearch.WordTrace tailWord_1433457 prefixEnd_1433457 736052438552103326595157 := by
  unfold tailWord_1433457
  simp only [CollatzResearch.WordTrace]
  refine ⟨52282471967837578809994625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34854981311891719206663083 52282471967837578809994625)
  ·
    refine ⟨39211853975878184107495969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52282471967837578809994625 39211853975878184107495969)
    ·
      refine ⟨29408890481908638080621977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39211853975878184107495969 29408890481908638080621977)
      ·
        refine ⟨22056667861431478560466483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29408890481908638080621977 22056667861431478560466483)
        ·
          refine ⟨33085001792147217840699725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22056667861431478560466483 33085001792147217840699725)
          ·
            refine ⟨12406875672055206690262397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33085001792147217840699725 12406875672055206690262397)
            ·
              refine ⟨4652578377020702508848399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12406875672055206690262397 4652578377020702508848399)
              ·
                refine ⟨6978867565531053763272599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652578377020702508848399 6978867565531053763272599)
                ·
                  refine ⟨10468301348296580644908899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978867565531053763272599 10468301348296580644908899)
                  ·
                    refine ⟨15702452022444870967363349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10468301348296580644908899 15702452022444870967363349)
                    ·
                      refine ⟨736052438552103326595157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15702452022444870967363349 736052438552103326595157)
                      ·
                        rfl

theorem cell23_1433457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1433457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433457 prefixEnd_1433457 := by exact prefixLift 1433457
  have htrace : WordTrace (prefixWord ++ tailWord_1433457) baseStart_1433457 baseEnd_1433457 := by
    simpa [prefixWord, tailWord_1433457, baseEnd_1433457] using wordTrace_append hprefix tailTrace_1433457
  have hstable : (prefixWord ++ tailWord_1433457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433457).length < 2 ^ (prefixWord ++ tailWord_1433457).sum := by decide
  have hdescent : baseEnd_1433457 < baseStart_1433457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433461 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1433461 : Nat := 118140960795 + 1433461 * 2 ^ 59
def prefixEnd_1433461 : Nat := 4983230072969 + 3 ^ 40 * 1433461 * 2
def baseEnd_1433461 : Nat := 736054492474721310945139

theorem tailTrace_1433461 : CollatzResearch.WordTrace tailWord_1433461 prefixEnd_1433461 736054492474721310945139 := by
  unfold tailWord_1433461
  simp only [CollatzResearch.WordTrace]
  refine ⟨52282617859823087493140237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34855078573215391662093491 52282617859823087493140237)
  ·
    refine ⟨19605981697433657809927589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52282617859823087493140237 19605981697433657809927589)
    ·
      refine ⟨3676121568268810839361423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19605981697433657809927589 3676121568268810839361423)
      ·
        refine ⟨5514182352403216259042135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676121568268810839361423 5514182352403216259042135)
        ·
          refine ⟨8271273528604824388563203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514182352403216259042135 8271273528604824388563203)
          ·
            refine ⟨12406910292907236582844805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271273528604824388563203 12406910292907236582844805)
            ·
              refine ⟨2326295679920106859283401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12406910292907236582844805 2326295679920106859283401)
              ·
                refine ⟨1744721759940080144462551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326295679920106859283401 1744721759940080144462551)
                ·
                  refine ⟨2617082639910120216693827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744721759940080144462551 2617082639910120216693827)
                  ·
                    refine ⟨3925623959865180325040741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617082639910120216693827 3925623959865180325040741)
                    ·
                      refine ⟨736054492474721310945139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3925623959865180325040741 736054492474721310945139)
                      ·
                        rfl

theorem cell23_1433461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1433461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433461 prefixEnd_1433461 := by exact prefixLift 1433461
  have htrace : WordTrace (prefixWord ++ tailWord_1433461) baseStart_1433461 baseEnd_1433461 := by
    simpa [prefixWord, tailWord_1433461, baseEnd_1433461] using wordTrace_append hprefix tailTrace_1433461
  have hstable : (prefixWord ++ tailWord_1433461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433461).length < 2 ^ (prefixWord ++ tailWord_1433461).sum := by decide
  have hdescent : baseEnd_1433461 < baseStart_1433461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433504 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2]
def baseStart_1433504 : Nat := 118140960795 + 1433504 * 2 ^ 59
def prefixEnd_1433504 : Nat := 4983230072969 + 3 ^ 40 * 1433504 * 2
def baseEnd_1433504 : Nat := 736076572142864642707441

theorem tailTrace_1433504 : CollatzResearch.WordTrace tailWord_1433504 prefixEnd_1433504 736076572142864642707441 := by
  unfold tailWord_1433504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142093099333652918477783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34856124132444870557970377 26142093099333652918477783)
  ·
    refine ⟨39213139649000479377716675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26142093099333652918477783 39213139649000479377716675)
    ·
      refine ⟨58819709473500719066575013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39213139649000479377716675 58819709473500719066575013)
      ·
        refine ⟨11028695526281384824982815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58819709473500719066575013 11028695526281384824982815)
        ·
          refine ⟨16543043289422077237474223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028695526281384824982815 16543043289422077237474223)
          ·
            refine ⟨24814564934133115856211335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543043289422077237474223 24814564934133115856211335)
            ·
              refine ⟨37221847401199673784317003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24814564934133115856211335 37221847401199673784317003)
              ·
                refine ⟨55832771101799510676475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37221847401199673784317003 55832771101799510676475505)
                ·
                  refine ⟨41874578326349633007356629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55832771101799510676475505 41874578326349633007356629)
                  ·
                    refine ⟨981435429523819523609921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41874578326349633007356629 981435429523819523609921)
                    ·
                      refine ⟨736076572142864642707441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981435429523819523609921 736076572142864642707441)
                      ·
                        rfl

theorem cell23_1433504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_1433504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433504 prefixEnd_1433504 := by exact prefixLift 1433504
  have htrace : WordTrace (prefixWord ++ tailWord_1433504) baseStart_1433504 baseEnd_1433504 := by
    simpa [prefixWord, tailWord_1433504, baseEnd_1433504] using wordTrace_append hprefix tailTrace_1433504
  have hstable : (prefixWord ++ tailWord_1433504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433504).length < 2 ^ (prefixWord ++ tailWord_1433504).sum := by decide
  have hdescent : baseEnd_1433504 < baseStart_1433504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433505 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1433505 : Nat := 118140960795 + 1433505 * 2 ^ 59
def prefixEnd_1433505 : Nat := 4983230072969 + 3 ^ 40 * 1433505 * 2
def baseEnd_1433505 : Nat := 245359028541173046264979

theorem tailTrace_1433505 : CollatzResearch.WordTrace tailWord_1433505 prefixEnd_1433505 245359028541173046264979 := by
  unfold tailWord_1433505
  simp only [CollatzResearch.WordTrace]
  refine ⟨52284222671663683007741969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34856148447775788671827979 52284222671663683007741969)
  ·
    refine ⟨39213167003747762255806477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52284222671663683007741969 39213167003747762255806477)
    ·
      refine ⟨14704937626405410845927429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39213167003747762255806477 14704937626405410845927429)
      ·
        refine ⟨2757175804951014533611393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14704937626405410845927429 2757175804951014533611393)
        ·
          refine ⟨2067881853713260900208545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757175804951014533611393 2067881853713260900208545)
          ·
            refine ⟨1550911390284945675156409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067881853713260900208545 1550911390284945675156409)
            ·
              refine ⟨1163183542713709256367307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550911390284945675156409 1163183542713709256367307)
              ·
                refine ⟨1744775314070563884550961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163183542713709256367307 1744775314070563884550961)
                ·
                  refine ⟨1308581485552922913413221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744775314070563884550961 1308581485552922913413221)
                  ·
                    refine ⟨245359028541173046264979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308581485552922913413221 245359028541173046264979)
                    ·
                      rfl

theorem cell23_1433505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1433505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433505 prefixEnd_1433505 := by exact prefixLift 1433505
  have htrace : WordTrace (prefixWord ++ tailWord_1433505) baseStart_1433505 baseEnd_1433505 := by
    simpa [prefixWord, tailWord_1433505, baseEnd_1433505] using wordTrace_append hprefix tailTrace_1433505
  have hstable : (prefixWord ++ tailWord_1433505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433505).length < 2 ^ (prefixWord ++ tailWord_1433505).sum := by decide
  have hdescent : baseEnd_1433505 < baseStart_1433505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433512 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1433512 : Nat := 118140960795 + 1433512 * 2 ^ 59
def prefixEnd_1433512 : Nat := 4983230072969 + 3 ^ 40 * 1433512 * 2
def baseEnd_1433512 : Nat := 736080679988100611407405

theorem tailTrace_1433512 : CollatzResearch.WordTrace tailWord_1433512 prefixEnd_1433512 736080679988100611407405 := by
  unfold tailWord_1433512
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142238991319161601623395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34856318655092215468831193 26142238991319161601623395)
  ·
    refine ⟨39213358486978742402435093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26142238991319161601623395 39213358486978742402435093)
    ·
      refine ⟨1838126179077128550114145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39213358486978742402435093 1838126179077128550114145)
      ·
        refine ⟨1378594634307846412585609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1838126179077128550114145 1378594634307846412585609)
        ·
          refine ⟨1033945975730884809439207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378594634307846412585609 1033945975730884809439207)
          ·
            refine ⟨1550918963596327214158811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033945975730884809439207 1550918963596327214158811)
            ·
              refine ⟨2326378445394490821238217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550918963596327214158811 2326378445394490821238217)
              ·
                refine ⟨1744783834045868115928663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326378445394490821238217 1744783834045868115928663)
                ·
                  refine ⟨2617175751068802173892995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744783834045868115928663 2617175751068802173892995)
                  ·
                    refine ⟨3925763626603203260839493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617175751068802173892995 3925763626603203260839493)
                    ·
                      refine ⟨736080679988100611407405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3925763626603203260839493 736080679988100611407405)
                      ·
                        rfl

theorem cell23_1433512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1433512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433512 prefixEnd_1433512 := by exact prefixLift 1433512
  have htrace : WordTrace (prefixWord ++ tailWord_1433512) baseStart_1433512 baseEnd_1433512 := by
    simpa [prefixWord, tailWord_1433512, baseEnd_1433512] using wordTrace_append hprefix tailTrace_1433512
  have hstable : (prefixWord ++ tailWord_1433512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433512).length < 2 ^ (prefixWord ++ tailWord_1433512).sum := by decide
  have hdescent : baseEnd_1433512 < baseStart_1433512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433527 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 6]
def baseStart_1433527 : Nat := 118140960795 + 1433527 * 2 ^ 59
def prefixEnd_1433527 : Nat := 4983230072969 + 3 ^ 40 * 1433527 * 2
def baseEnd_1433527 : Nat := 245362794065972684239945

theorem tailTrace_1433527 : CollatzResearch.WordTrace tailWord_1433527 prefixEnd_1433527 245362794065972684239945 := by
  unfold tailWord_1433527
  simp only [CollatzResearch.WordTrace]
  refine ⟨52285025077583980765042835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34856683385055987176695223 52285025077583980765042835)
  ·
    refine ⟨78427537616375971147564253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52285025077583980765042835 78427537616375971147564253)
    ·
      refine ⟨29410326606140989180336595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78427537616375971147564253 29410326606140989180336595)
      ·
        refine ⟨44115489909211483770504893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29410326606140989180336595 44115489909211483770504893)
        ·
          refine ⟨16543308715954306413939335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44115489909211483770504893 16543308715954306413939335)
          ·
            refine ⟨24814963073931459620909003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543308715954306413939335 24814963073931459620909003)
            ·
              refine ⟨37222444610897189431363505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24814963073931459620909003 37222444610897189431363505)
              ·
                refine ⟨27916833458172892073522629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37222444610897189431363505 27916833458172892073522629)
                ·
                  refine ⟨5234406273407417263785493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27916833458172892073522629 5234406273407417263785493)
                  ·
                    refine ⟨245362794065972684239945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5234406273407417263785493 245362794065972684239945)
                    ·
                      rfl

theorem cell23_1433527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_1433527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433527 prefixEnd_1433527 := by exact prefixLift 1433527
  have htrace : WordTrace (prefixWord ++ tailWord_1433527) baseStart_1433527 baseEnd_1433527 := by
    simpa [prefixWord, tailWord_1433527, baseEnd_1433527] using wordTrace_append hprefix tailTrace_1433527
  have hstable : (prefixWord ++ tailWord_1433527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433527).length < 2 ^ (prefixWord ++ tailWord_1433527).sum := by decide
  have hdescent : baseEnd_1433527 < baseStart_1433527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433614 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1433614 : Nat := 118140960795 + 1433614 * 2 ^ 59
def prefixEnd_1433614 : Nat := 4983230072969 + 3 ^ 40 * 1433614 * 2
def baseEnd_1433614 : Nat := 736133055014859212331935

theorem tailTrace_1433614 : CollatzResearch.WordTrace tailWord_1433614 prefixEnd_1433614 736133055014859212331935 := by
  unfold tailWord_1433614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536024778533599327932487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34858798818845863082306597 6536024778533599327932487)
  ·
    refine ⟨9804037167800398991898731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536024778533599327932487 9804037167800398991898731)
    ·
      refine ⟨14706055751700598487848097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804037167800398991898731 14706055751700598487848097)
      ·
        refine ⟨11029541813775448865886073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14706055751700598487848097 11029541813775448865886073)
        ·
          refine ⟨8272156360331586649414555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11029541813775448865886073 8272156360331586649414555)
          ·
            refine ⟨12408234540497379974121833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272156360331586649414555 12408234540497379974121833)
            ·
              refine ⟨9306175905373034980591375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12408234540497379974121833 9306175905373034980591375)
              ·
                refine ⟨13959263858059552470887063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306175905373034980591375 13959263858059552470887063)
                ·
                  refine ⟨20938895787089328706330595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13959263858059552470887063 20938895787089328706330595)
                  ·
                    refine ⟨31408343680633993059495893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20938895787089328706330595 31408343680633993059495893)
                    ·
                      refine ⟨736133055014859212331935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31408343680633993059495893 736133055014859212331935)
                      ·
                        rfl

theorem cell23_1433614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1433614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433614 prefixEnd_1433614 := by exact prefixLift 1433614
  have htrace : WordTrace (prefixWord ++ tailWord_1433614) baseStart_1433614 baseEnd_1433614 := by
    simpa [prefixWord, tailWord_1433614, baseEnd_1433614] using wordTrace_append hprefix tailTrace_1433614
  have hstable : (prefixWord ++ tailWord_1433614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433614).length < 2 ^ (prefixWord ++ tailWord_1433614).sum := by decide
  have hdescent : baseEnd_1433614 < baseStart_1433614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433624 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1433624 : Nat := 118140960795 + 1433624 * 2 ^ 59
def prefixEnd_1433624 : Nat := 4983230072969 + 3 ^ 40 * 1433624 * 2
def baseEnd_1433624 : Nat := 736138189821404173206889

theorem tailTrace_1433624 : CollatzResearch.WordTrace tailWord_1433624 prefixEnd_1433624 736138189821404173206889 := by
  unfold tailWord_1433624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26144281479116283165661963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34859041972155044220882617 26144281479116283165661963)
  ·
    refine ⟨39216422218674424748492945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26144281479116283165661963 39216422218674424748492945)
    ·
      refine ⟨29412316664005818561369709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39216422218674424748492945 29412316664005818561369709)
      ·
        refine ⟨11029618749002181960513641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29412316664005818561369709 11029618749002181960513641)
        ·
          refine ⟨8272214061751636470385231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11029618749002181960513641 8272214061751636470385231)
          ·
            refine ⟨12408321092627454705577847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272214061751636470385231 12408321092627454705577847)
            ·
              refine ⟨18612481638941182058366771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12408321092627454705577847 18612481638941182058366771)
              ·
                refine ⟨27918722458411773087550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18612481638941182058366771 27918722458411773087550157)
                ·
                  refine ⟨10469520921904414907831309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27918722458411773087550157 10469520921904414907831309)
                  ·
                    refine ⟨3926070345714155590436741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10469520921904414907831309 3926070345714155590436741)
                    ·
                      refine ⟨736138189821404173206889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3926070345714155590436741 736138189821404173206889)
                      ·
                        rfl

theorem cell23_1433624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1433624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433624 prefixEnd_1433624 := by exact prefixLift 1433624
  have htrace : WordTrace (prefixWord ++ tailWord_1433624) baseStart_1433624 baseEnd_1433624 := by
    simpa [prefixWord, tailWord_1433624, baseEnd_1433624] using wordTrace_append hprefix tailTrace_1433624
  have hstable : (prefixWord ++ tailWord_1433624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433624).length < 2 ^ (prefixWord ++ tailWord_1433624).sum := by decide
  have hdescent : baseEnd_1433624 < baseStart_1433624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433634 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1433634 : Nat := 118140960795 + 1433634 * 2 ^ 59
def prefixEnd_1433634 : Nat := 4983230072969 + 3 ^ 40 * 1433634 * 2
def baseEnd_1433634 : Nat := 245381108209316378027281

theorem tailTrace_1433634 : CollatzResearch.WordTrace tailWord_1433634 prefixEnd_1433634 245381108209316378027281 := by
  unfold tailWord_1433634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13072231922049084509796989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34859285125464225359458637 13072231922049084509796989)
  ·
    refine ⟨4902086970768406691173871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13072231922049084509796989 4902086970768406691173871)
    ·
      refine ⟨7353130456152610036760807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4902086970768406691173871 7353130456152610036760807)
      ·
        refine ⟨11029695684228915055141211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7353130456152610036760807 11029695684228915055141211)
        ·
          refine ⟨16544543526343372582711817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11029695684228915055141211 16544543526343372582711817)
          ·
            refine ⟨12408407644757529437033863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16544543526343372582711817 12408407644757529437033863)
            ·
              refine ⟨18612611467136294155550795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12408407644757529437033863 18612611467136294155550795)
              ·
                refine ⟨27918917200704441233326193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18612611467136294155550795 27918917200704441233326193)
                ·
                  refine ⟨20939187900528330924994645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27918917200704441233326193 20939187900528330924994645)
                  ·
                    refine ⟨245381108209316378027281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20939187900528330924994645 245381108209316378027281)
                    ·
                      rfl

theorem cell23_1433634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1433634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433634 prefixEnd_1433634 := by exact prefixLift 1433634
  have htrace : WordTrace (prefixWord ++ tailWord_1433634) baseStart_1433634 baseEnd_1433634 := by
    simpa [prefixWord, tailWord_1433634, baseEnd_1433634] using wordTrace_append hprefix tailTrace_1433634
  have hstable : (prefixWord ++ tailWord_1433634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433634).length < 2 ^ (prefixWord ++ tailWord_1433634).sum := by decide
  have hdescent : baseEnd_1433634 < baseStart_1433634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433664 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 8]
def baseStart_1433664 : Nat := 118140960795 + 1433664 * 2 ^ 59
def prefixEnd_1433664 : Nat := 4983230072969 + 3 ^ 40 * 1433664 * 2
def baseEnd_1433664 : Nat := 81795414338620446300745

theorem tailTrace_1433664 : CollatzResearch.WordTrace tailWord_1433664 prefixEnd_1433664 81795414338620446300745 := by
  unfold tailWord_1433664
  simp only [CollatzResearch.WordTrace]
  refine ⟨26145010939043826581390023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34860014585391768775186697 26145010939043826581390023)
  ·
    refine ⟨39217516408565739872085035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26145010939043826581390023 39217516408565739872085035)
    ·
      refine ⟨58826274612848609808127553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39217516408565739872085035 58826274612848609808127553)
      ·
        refine ⟨44119705959636457356095665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58826274612848609808127553 44119705959636457356095665)
        ·
          refine ⟨33089779469727343017071749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44119705959636457356095665 33089779469727343017071749)
          ·
            refine ⟨6204333650573876815700953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33089779469727343017071749 6204333650573876815700953)
            ·
              refine ⟨4653250237930407611775715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6204333650573876815700953 4653250237930407611775715)
              ·
                refine ⟨6979875356895611417663573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653250237930407611775715 6979875356895611417663573)
                ·
                  refine ⟨81795414338620446300745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6979875356895611417663573 81795414338620446300745)
                  ·
                    rfl

theorem cell23_1433664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_1433664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433664 prefixEnd_1433664 := by exact prefixLift 1433664
  have htrace : WordTrace (prefixWord ++ tailWord_1433664) baseStart_1433664 baseEnd_1433664 := by
    simpa [prefixWord, tailWord_1433664, baseEnd_1433664] using wordTrace_append hprefix tailTrace_1433664
  have hstable : (prefixWord ++ tailWord_1433664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433664).length < 2 ^ (prefixWord ++ tailWord_1433664).sum := by decide
  have hdescent : baseEnd_1433664 < baseStart_1433664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433731 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1433731 : Nat := 118140960795 + 1433731 * 2 ^ 59
def prefixEnd_1433731 : Nat := 4983230072969 + 3 ^ 40 * 1433731 * 2
def baseEnd_1433731 : Nat := 736193132251435254568897

theorem tailTrace_1433731 : CollatzResearch.WordTrace tailWord_1433731 prefixEnd_1433731 736193132251435254568897 := by
  unfold tailWord_1433731
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292465568844923605469047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34861643712563282403646031 52292465568844923605469047)
  ·
    refine ⟨78438698353267385408203571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52292465568844923605469047 78438698353267385408203571)
    ·
      refine ⟨117658047529901078112305357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78438698353267385408203571 117658047529901078112305357)
      ·
        refine ⟨44121767823712904292114509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117658047529901078112305357 44121767823712904292114509)
        ·
          refine ⟨16545662933892339109542941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44121767823712904292114509 16545662933892339109542941)
          ·
            refine ⟨6204623600209627166078603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16545662933892339109542941 6204623600209627166078603)
            ·
              refine ⟨9306935400314440749117905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204623600209627166078603 9306935400314440749117905)
              ·
                refine ⟨6980201550235830561838429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9306935400314440749117905 6980201550235830561838429)
                ·
                  refine ⟨2617575581338436460689411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6980201550235830561838429 2617575581338436460689411)
                  ·
                    refine ⟨3926363372007654691034117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617575581338436460689411 3926363372007654691034117)
                    ·
                      refine ⟨736193132251435254568897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3926363372007654691034117 736193132251435254568897)
                      ·
                        rfl

theorem cell23_1433731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1433731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433731 prefixEnd_1433731 := by exact prefixLift 1433731
  have htrace : WordTrace (prefixWord ++ tailWord_1433731) baseStart_1433731 baseEnd_1433731 := by
    simpa [prefixWord, tailWord_1433731, baseEnd_1433731] using wordTrace_append hprefix tailTrace_1433731
  have hstable : (prefixWord ++ tailWord_1433731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433731).length < 2 ^ (prefixWord ++ tailWord_1433731).sum := by decide
  have hdescent : baseEnd_1433731 < baseStart_1433731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433752 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1433752 : Nat := 118140960795 + 1433752 * 2 ^ 59
def prefixEnd_1433752 : Nat := 4983230072969 + 3 ^ 40 * 1433752 * 2
def baseEnd_1433752 : Nat := 736203915345179672406301

theorem tailTrace_1433752 : CollatzResearch.WordTrace tailWord_1433752 prefixEnd_1433752 736203915345179672406301 := by
  unfold tailWord_1433752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26146615750884422095991755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34862154334512562794655673 26146615750884422095991755)
  ·
    refine ⟨39219923626326633143987633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26146615750884422095991755 39219923626326633143987633)
    ·
      refine ⟨29414942719744974857990725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39219923626326633143987633 29414942719744974857990725)
      ·
        refine ⟨5515301759952182785873261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29414942719744974857990725 5515301759952182785873261)
        ·
          refine ⟨2068238159982068544702473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5515301759952182785873261 2068238159982068544702473)
          ·
            refine ⟨1551178619986551408526855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2068238159982068544702473 1551178619986551408526855)
            ·
              refine ⟨2326767929979827112790283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551178619986551408526855 2326767929979827112790283)
              ·
                refine ⟨3490151894969740669185425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326767929979827112790283 3490151894969740669185425)
                ·
                  refine ⟨2617613921227305501889069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3490151894969740669185425 2617613921227305501889069)
                  ·
                    refine ⟨981605220460239563208401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617613921227305501889069 981605220460239563208401)
                    ·
                      refine ⟨736203915345179672406301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981605220460239563208401 736203915345179672406301)
                      ·
                        rfl

theorem cell23_1433752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1433752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433752 prefixEnd_1433752 := by exact prefixLift 1433752
  have htrace : WordTrace (prefixWord ++ tailWord_1433752) baseStart_1433752 baseEnd_1433752 := by
    simpa [prefixWord, tailWord_1433752, baseEnd_1433752] using wordTrace_append hprefix tailTrace_1433752
  have hstable : (prefixWord ++ tailWord_1433752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433752).length < 2 ^ (prefixWord ++ tailWord_1433752).sum := by decide
  have hdescent : baseEnd_1433752 < baseStart_1433752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433762 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1433762 : Nat := 118140960795 + 1433762 * 2 ^ 59
def prefixEnd_1433762 : Nat := 4983230072969 + 3 ^ 40 * 1433762 * 2
def baseEnd_1433762 : Nat := 245403016717241544427085

theorem tailTrace_1433762 : CollatzResearch.WordTrace tailWord_1433762 prefixEnd_1433762 245403016717241544427085 := by
  unfold tailWord_1433762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073399057933153974961885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34862397487821743933231693 13073399057933153974961885)
  ·
    refine ⟨4902524646724932740610707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13073399057933153974961885 4902524646724932740610707)
    ·
      refine ⟨7353786970087399110916061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4902524646724932740610707 7353786970087399110916061)
      ·
        refine ⟨2757670113782774666593523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7353786970087399110916061 2757670113782774666593523)
        ·
          refine ⟨4136505170674161999890285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757670113782774666593523 4136505170674161999890285)
          ·
            refine ⟨1551189439002810749958857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4136505170674161999890285 1551189439002810749958857)
            ·
              refine ⟨1163392079252108062469143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551189439002810749958857 1163392079252108062469143)
              ·
                refine ⟨1745088118878162093703715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163392079252108062469143 1745088118878162093703715)
                ·
                  refine ⟨2617632178317243140555573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745088118878162093703715 2617632178317243140555573)
                  ·
                    refine ⟨245403016717241544427085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2617632178317243140555573 245403016717241544427085)
                    ·
                      rfl

theorem cell23_1433762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1433762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433762 prefixEnd_1433762 := by exact prefixLift 1433762
  have htrace : WordTrace (prefixWord ++ tailWord_1433762) baseStart_1433762 baseEnd_1433762 := by
    simpa [prefixWord, tailWord_1433762, baseEnd_1433762] using wordTrace_append hprefix tailTrace_1433762
  have hstable : (prefixWord ++ tailWord_1433762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433762).length < 2 ^ (prefixWord ++ tailWord_1433762).sum := by decide
  have hdescent : baseEnd_1433762 < baseStart_1433762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433825 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_1433825 : Nat := 118140960795 + 1433825 * 2 ^ 59
def prefixEnd_1433825 : Nat := 4983230072969 + 3 ^ 40 * 1433825 * 2
def baseEnd_1433825 : Nat := 736241399432957886793465

theorem tailTrace_1433825 : CollatzResearch.WordTrace tailWord_1433825 prefixEnd_1433825 736241399432957886793465 := by
  unfold tailWord_1433825
  simp only [CollatzResearch.WordTrace]
  refine ⟨52295894030504377659390929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34863929353669585106260619 52295894030504377659390929)
  ·
    refine ⟨39221920522878283244543197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52295894030504377659390929 39221920522878283244543197)
    ·
      refine ⟨14708220196079356216703699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39221920522878283244543197 14708220196079356216703699)
      ·
        refine ⟨22062330294119034325055549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14708220196079356216703699 22062330294119034325055549)
        ·
          refine ⟨8273373860294637871895831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22062330294119034325055549 8273373860294637871895831)
          ·
            refine ⟨12410060790441956807843747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273373860294637871895831 12410060790441956807843747)
            ·
              refine ⟨18615091185662935211765621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12410060790441956807843747 18615091185662935211765621)
              ·
                refine ⟨1745164798655900176103027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18615091185662935211765621 1745164798655900176103027)
                ·
                  refine ⟨2617747197983850264154541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745164798655900176103027 2617747197983850264154541)
                  ·
                    refine ⟨981655199243943849057953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617747197983850264154541 981655199243943849057953)
                    ·
                      refine ⟨736241399432957886793465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981655199243943849057953 736241399432957886793465)
                      ·
                        rfl

theorem cell23_1433825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_1433825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433825 prefixEnd_1433825 := by exact prefixLift 1433825
  have htrace : WordTrace (prefixWord ++ tailWord_1433825) baseStart_1433825 baseEnd_1433825 := by
    simpa [prefixWord, tailWord_1433825, baseEnd_1433825] using wordTrace_append hprefix tailTrace_1433825
  have hstable : (prefixWord ++ tailWord_1433825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433825).length < 2 ^ (prefixWord ++ tailWord_1433825).sum := by decide
  have hdescent : baseEnd_1433825 < baseStart_1433825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433902 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1433902 : Nat := 118140960795 + 1433902 * 2 ^ 59
def prefixEnd_1433902 : Nat := 4983230072969 + 3 ^ 40 * 1433902 * 2
def baseEnd_1433902 : Nat := 736280937443354085530611

theorem tailTrace_1433902 : CollatzResearch.WordTrace tailWord_1433902 prefixEnd_1433902 736280937443354085530611 := by
  unfold tailWord_1433902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537337806403177476242995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34865801634150279873295973 6537337806403177476242995)
  ·
    refine ⟨9806006709604766214364493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537337806403177476242995 9806006709604766214364493)
    ·
      refine ⟨3677252516101787330386685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9806006709604766214364493 3677252516101787330386685)
      ·
        refine ⟨1378969693538170248895007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3677252516101787330386685 1378969693538170248895007)
        ·
          refine ⟨2068454540307255373342511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378969693538170248895007 2068454540307255373342511)
          ·
            refine ⟨3102681810460883060013767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068454540307255373342511 3102681810460883060013767)
            ·
              refine ⟨4654022715691324590020651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102681810460883060013767 4654022715691324590020651)
              ·
                refine ⟨6981034073536986885030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654022715691324590020651 6981034073536986885030977)
                ·
                  refine ⟨5235775555152740163773233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981034073536986885030977 5235775555152740163773233)
                  ·
                    refine ⟨3926831666364555122829925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5235775555152740163773233 3926831666364555122829925)
                    ·
                      refine ⟨736280937443354085530611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3926831666364555122829925 736280937443354085530611)
                      ·
                        rfl

theorem cell23_1433902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1433902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433902 prefixEnd_1433902 := by exact prefixLift 1433902
  have htrace : WordTrace (prefixWord ++ tailWord_1433902) baseStart_1433902 baseEnd_1433902 := by
    simpa [prefixWord, tailWord_1433902, baseEnd_1433902] using wordTrace_append hprefix tailTrace_1433902
  have hstable : (prefixWord ++ tailWord_1433902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433902).length < 2 ^ (prefixWord ++ tailWord_1433902).sum := by decide
  have hdescent : baseEnd_1433902 < baseStart_1433902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433905 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1433905 : Nat := 118140960795 + 1433905 * 2 ^ 59
def prefixEnd_1433905 : Nat := 4983230072969 + 3 ^ 40 * 1433905 * 2
def baseEnd_1433905 : Nat := 736282477885317573793097

theorem tailTrace_1433905 : CollatzResearch.WordTrace tailWord_1433905 prefixEnd_1433905 736282477885317573793097 := by
  unfold tailWord_1433905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298811870214551322303169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34865874580143034214868779 52298811870214551322303169)
  ·
    refine ⟨39224108902660913491727377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52298811870214551322303169 39224108902660913491727377)
    ·
      refine ⟨29418081676995685118795533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39224108902660913491727377 29418081676995685118795533)
      ·
        refine ⟨11031780628873381919548325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29418081676995685118795533 11031780628873381919548325)
        ·
          refine ⟨2068458867913759109915311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11031780628873381919548325 2068458867913759109915311)
          ·
            refine ⟨3102688301870638664872967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068458867913759109915311 3102688301870638664872967)
            ·
              refine ⟨4654032452805957997309451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102688301870638664872967 4654032452805957997309451)
              ·
                refine ⟨6981048679208936995964177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654032452805957997309451 6981048679208936995964177)
                ·
                  refine ⟨5235786509406702746973133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981048679208936995964177 5235786509406702746973133)
                  ·
                    refine ⟨1963419941027513530114925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5235786509406702746973133 1963419941027513530114925)
                    ·
                      refine ⟨736282477885317573793097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963419941027513530114925 736282477885317573793097)
                      ·
                        rfl

theorem cell23_1433905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1433905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433905 prefixEnd_1433905 := by exact prefixLift 1433905
  have htrace : WordTrace (prefixWord ++ tailWord_1433905) baseStart_1433905 baseEnd_1433905 := by
    simpa [prefixWord, tailWord_1433905, baseEnd_1433905] using wordTrace_append hprefix tailTrace_1433905
  have hstable : (prefixWord ++ tailWord_1433905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433905).length < 2 ^ (prefixWord ++ tailWord_1433905).sum := by decide
  have hdescent : baseEnd_1433905 < baseStart_1433905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433931 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_1433931 : Nat := 118140960795 + 1433931 * 2 ^ 59
def prefixEnd_1433931 : Nat := 4983230072969 + 3 ^ 40 * 1433931 * 2
def baseEnd_1433931 : Nat := 736295828382334472067977

theorem tailTrace_1433931 : CollatzResearch.WordTrace tailWord_1433931 prefixEnd_1433931 736295828382334472067977 := by
  unfold tailWord_1433931
  simp only [CollatzResearch.WordTrace]
  refine ⟨52299760168120357762749647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34866506778746905175166431 52299760168120357762749647)
  ·
    refine ⟨78449640252180536644124471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52299760168120357762749647 78449640252180536644124471)
    ·
      refine ⟨117674460378270804966186707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78449640252180536644124471 117674460378270804966186707)
      ·
        refine ⟨176511690567406207449280061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117674460378270804966186707 176511690567406207449280061)
        ·
          refine ⟨66191883962777327793480023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176511690567406207449280061 66191883962777327793480023)
          ·
            refine ⟨99287825944165991690220035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66191883962777327793480023 99287825944165991690220035)
            ·
              refine ⟨148931738916248987535330053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99287825944165991690220035 148931738916248987535330053)
              ·
                refine ⟨27924701046796685162874385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148931738916248987535330053 27924701046796685162874385)
                ·
                  refine ⟨20943525785097513872155789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27924701046796685162874385 20943525785097513872155789)
                  ·
                    refine ⟨7853822169411567702058421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20943525785097513872155789 7853822169411567702058421)
                    ·
                      refine ⟨736295828382334472067977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7853822169411567702058421 736295828382334472067977)
                      ·
                        rfl

theorem cell23_1433931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_1433931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433931 prefixEnd_1433931 := by exact prefixLift 1433931
  have htrace : WordTrace (prefixWord ++ tailWord_1433931) baseStart_1433931 baseEnd_1433931 := by
    simpa [prefixWord, tailWord_1433931, baseEnd_1433931] using wordTrace_append hprefix tailTrace_1433931
  have hstable : (prefixWord ++ tailWord_1433931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433931).length < 2 ^ (prefixWord ++ tailWord_1433931).sum := by decide
  have hdescent : baseEnd_1433931 < baseStart_1433931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433955 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 3, 4]
def baseStart_1433955 : Nat := 118140960795 + 1433955 * 2 ^ 59
def prefixEnd_1433955 : Nat := 4983230072969 + 3 ^ 40 * 1433955 * 2
def baseEnd_1433955 : Nat := 245436050639347459389289

theorem tailTrace_1433955 : CollatzResearch.WordTrace tailWord_1433955 prefixEnd_1433955 245436050639347459389289 := by
  unfold tailWord_1433955
  simp only [CollatzResearch.WordTrace]
  refine ⟨52300635520033409861623319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34867090346688939907748879 52300635520033409861623319)
  ·
    refine ⟨78450953280050114792434979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52300635520033409861623319 78450953280050114792434979)
    ·
      refine ⟨117676429920075172188652469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78450953280050114792434979 117676429920075172188652469)
      ·
        refine ⟨11032165305007047392686169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117676429920075172188652469 11032165305007047392686169)
        ·
          refine ⟨8274123978755285544514627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11032165305007047392686169 8274123978755285544514627)
          ·
            refine ⟨12411185968132928316771941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274123978755285544514627 12411185968132928316771941)
            ·
              refine ⟨2327097369024924059394739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12411185968132928316771941 2327097369024924059394739)
              ·
                refine ⟨3490646053537386089092109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327097369024924059394739 3490646053537386089092109)
                ·
                  refine ⟨1308992270076519783409541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3490646053537386089092109 1308992270076519783409541)
                  ·
                    refine ⟨245436050639347459389289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308992270076519783409541 245436050639347459389289)
                    ·
                      rfl

theorem cell23_1433955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 4].length) (baseStart_1433955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433955 prefixEnd_1433955 := by exact prefixLift 1433955
  have htrace : WordTrace (prefixWord ++ tailWord_1433955) baseStart_1433955 baseEnd_1433955 := by
    simpa [prefixWord, tailWord_1433955, baseEnd_1433955] using wordTrace_append hprefix tailTrace_1433955
  have hstable : (prefixWord ++ tailWord_1433955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433955).length < 2 ^ (prefixWord ++ tailWord_1433955).sum := by decide
  have hdescent : baseEnd_1433955 < baseStart_1433955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433962 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1433962 : Nat := 118140960795 + 1433962 * 2 ^ 59
def prefixEnd_1433962 : Nat := 4983230072969 + 3 ^ 40 * 1433962 * 2
def baseEnd_1433962 : Nat := 736311746282623850780335

theorem tailTrace_1433962 : CollatzResearch.WordTrace tailWord_1433962 prefixEnd_1433962 736311746282623850780335 := by
  unfold tailWord_1433962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075222707752012514282035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34867260554005366704752093 13075222707752012514282035)
  ·
    refine ⟨19612834061628018771423053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13075222707752012514282035 19612834061628018771423053)
    ·
      refine ⟨7354812773110507039283645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19612834061628018771423053 7354812773110507039283645)
      ·
        refine ⟨2758054789916440139731367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7354812773110507039283645 2758054789916440139731367)
        ·
          refine ⟨4137082184874660209597051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758054789916440139731367 4137082184874660209597051)
          ·
            refine ⟨6205623277311990314395577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137082184874660209597051 6205623277311990314395577)
            ·
              refine ⟨4654217457983992735796683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6205623277311990314395577 4654217457983992735796683)
              ·
                refine ⟨6981326186975989103695025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654217457983992735796683 6981326186975989103695025)
                ·
                  refine ⟨5235994640231991827771269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981326186975989103695025 5235994640231991827771269)
                  ·
                    refine ⟨981748995043498467707113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235994640231991827771269 981748995043498467707113)
                    ·
                      refine ⟨736311746282623850780335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981748995043498467707113 736311746282623850780335)
                      ·
                        rfl

theorem cell23_1433962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1433962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1433962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1433962 prefixEnd_1433962 := by exact prefixLift 1433962
  have htrace : WordTrace (prefixWord ++ tailWord_1433962) baseStart_1433962 baseEnd_1433962 := by
    simpa [prefixWord, tailWord_1433962, baseEnd_1433962] using wordTrace_append hprefix tailTrace_1433962
  have hstable : (prefixWord ++ tailWord_1433962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433962).length < 2 ^ (prefixWord ++ tailWord_1433962).sum := by decide
  have hdescent : baseEnd_1433962 < baseStart_1433962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434028 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1434028 : Nat := 118140960795 + 1434028 * 2 ^ 59
def prefixEnd_1434028 : Nat := 4983230072969 + 3 ^ 40 * 1434028 * 2
def baseEnd_1434028 : Nat := 245448545335273530851677

theorem tailTrace_1434028 : CollatzResearch.WordTrace tailWord_1434028 prefixEnd_1434028 245448545335273530851677 := by
  unfold tailWord_1434028
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151649024384471664515369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34868865365845962219353825 26151649024384471664515369)
  ·
    refine ⟨19613736768288353748386527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26151649024384471664515369 19613736768288353748386527)
    ·
      refine ⟨29420605152432530622579791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19613736768288353748386527 29420605152432530622579791)
      ·
        refine ⟨44130907728648795933869687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29420605152432530622579791 44130907728648795933869687)
        ·
          refine ⟨66196361592973193900804531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44130907728648795933869687 66196361592973193900804531)
          ·
            refine ⟨99294542389459790851206797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66196361592973193900804531 99294542389459790851206797)
            ·
              refine ⟨37235453396047421569202549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99294542389459790851206797 37235453396047421569202549)
              ·
                refine ⟨3490823755879445772112739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37235453396047421569202549 3490823755879445772112739)
                ·
                  refine ⟨5236235633819168658169109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490823755879445772112739 5236235633819168658169109)
                  ·
                    refine ⟨245448545335273530851677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5236235633819168658169109 245448545335273530851677)
                    ·
                      rfl

theorem cell23_1434028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1434028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434028 prefixEnd_1434028 := by exact prefixLift 1434028
  have htrace : WordTrace (prefixWord ++ tailWord_1434028) baseStart_1434028 baseEnd_1434028 := by
    simpa [prefixWord, tailWord_1434028, baseEnd_1434028] using wordTrace_append hprefix tailTrace_1434028
  have hstable : (prefixWord ++ tailWord_1434028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434028).length < 2 ^ (prefixWord ++ tailWord_1434028).sum := by decide
  have hdescent : baseEnd_1434028 < baseStart_1434028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434045 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1434045 : Nat := 118140960795 + 1434045 * 2 ^ 59
def prefixEnd_1434045 : Nat := 4983230072969 + 3 ^ 40 * 1434045 * 2
def baseEnd_1434045 : Nat := 245451455058982342014151

theorem tailTrace_1434045 : CollatzResearch.WordTrace tailWord_1434045 prefixEnd_1434045 245451455058982342014151 := by
  unfold tailWord_1434045
  simp only [CollatzResearch.WordTrace]
  refine ⟨52303918089707355232399589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34869278726471570154933059 52303918089707355232399589)
  ·
    refine ⟨9806984641820129106074923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52303918089707355232399589 9806984641820129106074923)
    ·
      refine ⟨14710476962730193659112385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806984641820129106074923 14710476962730193659112385)
      ·
        refine ⟨11032857722047645244334289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14710476962730193659112385 11032857722047645244334289)
        ·
          refine ⟨8274643291535733933250717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11032857722047645244334289 8274643291535733933250717)
          ·
            refine ⟨3102991234325900224969019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8274643291535733933250717 3102991234325900224969019)
            ·
              refine ⟨4654486851488850337453529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102991234325900224969019 4654486851488850337453529)
              ·
                refine ⟨3490865138616637753090147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4654486851488850337453529 3490865138616637753090147)
                ·
                  refine ⟨5236297707924956629635221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490865138616637753090147 5236297707924956629635221)
                  ·
                    refine ⟨245451455058982342014151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5236297707924956629635221 245451455058982342014151)
                    ·
                      rfl

theorem cell23_1434045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1434045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434045 prefixEnd_1434045 := by exact prefixLift 1434045
  have htrace : WordTrace (prefixWord ++ tailWord_1434045) baseStart_1434045 baseEnd_1434045 := by
    simpa [prefixWord, tailWord_1434045, baseEnd_1434045] using wordTrace_append hprefix tailTrace_1434045
  have hstable : (prefixWord ++ tailWord_1434045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434045).length < 2 ^ (prefixWord ++ tailWord_1434045).sum := by decide
  have hdescent : baseEnd_1434045 < baseStart_1434045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434055 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1434055 : Nat := 118140960795 + 1434055 * 2 ^ 59
def prefixEnd_1434055 : Nat := 4983230072969 + 3 ^ 40 * 1434055 * 2
def baseEnd_1434055 : Nat := 736359499983491986917407

theorem tailTrace_1434055 : CollatzResearch.WordTrace tailWord_1434055 prefixEnd_1434055 736359499983491986917407 := by
  unfold tailWord_1434055
  simp only [CollatzResearch.WordTrace]
  refine ⟨52304282819671126940263619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34869521879780751293509079 52304282819671126940263619)
  ·
    refine ⟨78456424229506690410395429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52304282819671126940263619 78456424229506690410395429)
    ·
      refine ⟨14710579543032504451949143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78456424229506690410395429 14710579543032504451949143)
      ·
        refine ⟨22065869314548756677923715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14710579543032504451949143 22065869314548756677923715)
        ·
          refine ⟨33098803971823135016885573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22065869314548756677923715 33098803971823135016885573)
          ·
            refine ⟨6206025744716837815666045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33098803971823135016885573 6206025744716837815666045)
            ·
              refine ⟨2327259654268814180874767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6206025744716837815666045 2327259654268814180874767)
              ·
                refine ⟨3490889481403221271312151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327259654268814180874767 3490889481403221271312151)
                ·
                  refine ⟨5236334222104831906968227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490889481403221271312151 5236334222104831906968227)
                  ·
                    refine ⟨7854501333157247860452341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236334222104831906968227 7854501333157247860452341)
                    ·
                      refine ⟨736359499983491986917407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7854501333157247860452341 736359499983491986917407)
                      ·
                        rfl

theorem cell23_1434055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1434055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434055 prefixEnd_1434055 := by exact prefixLift 1434055
  have htrace : WordTrace (prefixWord ++ tailWord_1434055) baseStart_1434055 baseEnd_1434055 := by
    simpa [prefixWord, tailWord_1434055, baseEnd_1434055] using wordTrace_append hprefix tailTrace_1434055
  have hstable : (prefixWord ++ tailWord_1434055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434055).length < 2 ^ (prefixWord ++ tailWord_1434055).sum := by decide
  have hdescent : baseEnd_1434055 < baseStart_1434055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434102 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1434102 : Nat := 118140960795 + 1434102 * 2 ^ 59
def prefixEnd_1434102 : Nat := 4983230072969 + 3 ^ 40 * 1434102 * 2
def baseEnd_1434102 : Nat := 736383633574253303029691

theorem tailTrace_1434102 : CollatzResearch.WordTrace tailWord_1434102 prefixEnd_1434102 736383633574253303029691 := by
  unfold tailWord_1434102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269124815656303372951535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34870664700333902644816373 3269124815656303372951535)
  ·
    refine ⟨4903687223484455059427303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269124815656303372951535 4903687223484455059427303)
    ·
      refine ⟨7355530835226682589140955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903687223484455059427303 7355530835226682589140955)
      ·
        refine ⟨11033296252840023883711433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355530835226682589140955 11033296252840023883711433)
        ·
          refine ⟨8274972189630017912783575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11033296252840023883711433 8274972189630017912783575)
          ·
            refine ⟨12412458284445026869175363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274972189630017912783575 12412458284445026869175363)
            ·
              refine ⟨18618687426667540303763045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12412458284445026869175363 18618687426667540303763045)
              ·
                refine ⟨3491003892500163806955571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18618687426667540303763045 3491003892500163806955571)
                ·
                  refine ⟨5236505838750245710433357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491003892500163806955571 5236505838750245710433357)
                  ·
                    refine ⟨1963689689531342141412509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5236505838750245710433357 1963689689531342141412509)
                    ·
                      refine ⟨736383633574253303029691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963689689531342141412509 736383633574253303029691)
                      ·
                        rfl

theorem cell23_1434102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1434102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434102 prefixEnd_1434102 := by exact prefixLift 1434102
  have htrace : WordTrace (prefixWord ++ tailWord_1434102) baseStart_1434102 baseEnd_1434102 := by
    simpa [prefixWord, tailWord_1434102, baseEnd_1434102] using wordTrace_append hprefix tailTrace_1434102
  have hstable : (prefixWord ++ tailWord_1434102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434102).length < 2 ^ (prefixWord ++ tailWord_1434102).sum := by decide
  have hdescent : baseEnd_1434102 < baseStart_1434102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434119 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1434119 : Nat := 118140960795 + 1434119 * 2 ^ 59
def prefixEnd_1434119 : Nat := 4983230072969 + 3 ^ 40 * 1434119 * 2
def baseEnd_1434119 : Nat := 736392362745379736517113

theorem tailTrace_1434119 : CollatzResearch.WordTrace tailWord_1434119 prefixEnd_1434119 736392362745379736517113 := by
  unfold tailWord_1434119
  simp only [CollatzResearch.WordTrace]
  refine ⟨52306617091439265870593411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34871078060959510580395607 52306617091439265870593411)
  ·
    refine ⟨78459925637158898805890117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52306617091439265870593411 78459925637158898805890117)
    ·
      refine ⟨14711236056967293526104397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78459925637158898805890117 14711236056967293526104397)
      ·
        refine ⟨5516713521362735072289149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14711236056967293526104397 5516713521362735072289149)
        ·
          refine ⟨2068767570511025652108431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5516713521362735072289149 2068767570511025652108431)
          ·
            refine ⟨3103151355766538478162647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068767570511025652108431 3103151355766538478162647)
            ·
              refine ⟨4654727033649807717243971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103151355766538478162647 4654727033649807717243971)
              ·
                refine ⟨6982090550474711575865957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654727033649807717243971 6982090550474711575865957)
                ·
                  refine ⟨1309141978214008420474867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6982090550474711575865957 1309141978214008420474867)
                  ·
                    refine ⟨1963712967321012630712301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309141978214008420474867 1963712967321012630712301)
                    ·
                      refine ⟨736392362745379736517113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963712967321012630712301 736392362745379736517113)
                      ·
                        rfl

theorem cell23_1434119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1434119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434119 prefixEnd_1434119 := by exact prefixLift 1434119
  have htrace : WordTrace (prefixWord ++ tailWord_1434119) baseStart_1434119 baseEnd_1434119 := by
    simpa [prefixWord, tailWord_1434119, baseEnd_1434119] using wordTrace_append hprefix tailTrace_1434119
  have hstable : (prefixWord ++ tailWord_1434119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434119).length < 2 ^ (prefixWord ++ tailWord_1434119).sum := by decide
  have hdescent : baseEnd_1434119 < baseStart_1434119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434136 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1434136 : Nat := 118140960795 + 1434136 * 2 ^ 59
def prefixEnd_1434136 : Nat := 4983230072969 + 3 ^ 40 * 1434136 * 2
def baseEnd_1434136 : Nat := 736401091916506170004535

theorem tailTrace_1434136 : CollatzResearch.WordTrace tailWord_1434136 prefixEnd_1434136 736401091916506170004535 := by
  unfold tailWord_1434136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153618566188838886981131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34871491421585118515974841 26153618566188838886981131)
  ·
    refine ⟨39230427849283258330471697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26153618566188838886981131 39230427849283258330471697)
    ·
      refine ⟨29422820886962443747853773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39230427849283258330471697 29422820886962443747853773)
      ·
        refine ⟨11033557832610916405445165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29422820886962443747853773 11033557832610916405445165)
        ·
          refine ⟨4137584187229093652041937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11033557832610916405445165 4137584187229093652041937)
          ·
            refine ⟨3103188140421820239031453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137584187229093652041937 3103188140421820239031453)
            ·
              refine ⟨1163695552658182589636795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3103188140421820239031453 1163695552658182589636795)
              ·
                refine ⟨1745543328987273884455193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163695552658182589636795 1745543328987273884455193)
                ·
                  refine ⟨1309157496740455413341395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745543328987273884455193 1309157496740455413341395)
                  ·
                    refine ⟨1963736245110683120012093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309157496740455413341395 1963736245110683120012093)
                    ·
                      refine ⟨736401091916506170004535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963736245110683120012093 736401091916506170004535)
                      ·
                        rfl

theorem cell23_1434136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1434136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434136 prefixEnd_1434136 := by exact prefixLift 1434136
  have htrace : WordTrace (prefixWord ++ tailWord_1434136) baseStart_1434136 baseEnd_1434136 := by
    simpa [prefixWord, tailWord_1434136, baseEnd_1434136] using wordTrace_append hprefix tailTrace_1434136
  have hstable : (prefixWord ++ tailWord_1434136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434136).length < 2 ^ (prefixWord ++ tailWord_1434136).sum := by decide
  have hdescent : baseEnd_1434136 < baseStart_1434136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434145 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1434145 : Nat := 118140960795 + 1434145 * 2 ^ 59
def prefixEnd_1434145 : Nat := 4983230072969 + 3 ^ 40 * 1434145 * 2
def baseEnd_1434145 : Nat := 736405713242396634791993

theorem tailTrace_1434145 : CollatzResearch.WordTrace tailWord_1434145 prefixEnd_1434145 736405713242396634791993 := by
  unfold tailWord_1434145
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307565389345072311039889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34871710259563381540693259 52307565389345072311039889)
  ·
    refine ⟨39230674042008804233279917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52307565389345072311039889 39230674042008804233279917)
    ·
      refine ⟨14711502765753301587479969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39230674042008804233279917 14711502765753301587479969)
      ·
        refine ⟨11033627074314976190609977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14711502765753301587479969 11033627074314976190609977)
        ·
          refine ⟨8275220305736232142957483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11033627074314976190609977 8275220305736232142957483)
          ·
            refine ⟨12412830458604348214436225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275220305736232142957483 12412830458604348214436225)
            ·
              refine ⟨9309622843953261160827169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12412830458604348214436225 9309622843953261160827169)
              ·
                refine ⟨6982217132964945870620377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9309622843953261160827169 6982217132964945870620377)
                ·
                  refine ⟨5236662849723709402965283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6982217132964945870620377 5236662849723709402965283)
                  ·
                    refine ⟨7854994274585564104447925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236662849723709402965283 7854994274585564104447925)
                    ·
                      refine ⟨736405713242396634791993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7854994274585564104447925 736405713242396634791993)
                      ·
                        rfl

theorem cell23_1434145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1434145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434145 prefixEnd_1434145 := by exact prefixLift 1434145
  have htrace : WordTrace (prefixWord ++ tailWord_1434145) baseStart_1434145 baseEnd_1434145 := by
    simpa [prefixWord, tailWord_1434145, baseEnd_1434145] using wordTrace_append hprefix tailTrace_1434145
  have hstable : (prefixWord ++ tailWord_1434145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434145).length < 2 ^ (prefixWord ++ tailWord_1434145).sum := by decide
  have hdescent : baseEnd_1434145 < baseStart_1434145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434193 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_1434193 : Nat := 118140960795 + 1434193 * 2 ^ 59
def prefixEnd_1434193 : Nat := 4983230072969 + 3 ^ 40 * 1434193 * 2
def baseEnd_1434193 : Nat := 736430360313812446991773

theorem tailTrace_1434193 : CollatzResearch.WordTrace tailWord_1434193 prefixEnd_1434193 736430360313812446991773 := by
  unfold tailWord_1434193
  simp only [CollatzResearch.WordTrace]
  refine ⟨52309316093171176508787233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34872877395447451005858155 52309316093171176508787233)
  ·
    refine ⟨39231987069878382381590425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52309316093171176508787233 39231987069878382381590425)
    ·
      refine ⟨29423990302408786786192819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39231987069878382381590425 29423990302408786786192819)
      ·
        refine ⟨44135985453613180179289229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29423990302408786786192819 44135985453613180179289229)
        ·
          refine ⟨16550994545104942567233461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44135985453613180179289229 16550994545104942567233461)
          ·
            refine ⟨1551655738603588365678137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16550994545104942567233461 1551655738603588365678137)
            ·
              refine ⟨1163741803952691274258603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551655738603588365678137 1163741803952691274258603)
              ·
                refine ⟨1745612705929036911387905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163741803952691274258603 1745612705929036911387905)
                ·
                  refine ⟨1309209529446777683540929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745612705929036911387905 1309209529446777683540929)
                  ·
                    refine ⟨981907147085083262655697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1309209529446777683540929 981907147085083262655697)
                    ·
                      refine ⟨736430360313812446991773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981907147085083262655697 736430360313812446991773)
                      ·
                        rfl

theorem cell23_1434193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_1434193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434193 prefixEnd_1434193 := by exact prefixLift 1434193
  have htrace : WordTrace (prefixWord ++ tailWord_1434193) baseStart_1434193 baseEnd_1434193 := by
    simpa [prefixWord, tailWord_1434193, baseEnd_1434193] using wordTrace_append hprefix tailTrace_1434193
  have hstable : (prefixWord ++ tailWord_1434193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434193).length < 2 ^ (prefixWord ++ tailWord_1434193).sum := by decide
  have hdescent : baseEnd_1434193 < baseStart_1434193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434212 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1434212 : Nat := 118140960795 + 1434212 * 2 ^ 59
def prefixEnd_1434212 : Nat := 4983230072969 + 3 ^ 40 * 1434212 * 2
def baseEnd_1434212 : Nat := 245480038815415957551395

theorem tailTrace_1434212 : CollatzResearch.WordTrace tailWord_1434212 prefixEnd_1434212 245480038815415957551395 := by
  unfold tailWord_1434212
  simp only [CollatzResearch.WordTrace]
  refine ⟨26155004540051171376864445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34873339386734895169152593 26155004540051171376864445)
  ·
    refine ⟨9808126702519189266324167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26155004540051171376864445 9808126702519189266324167)
    ·
      refine ⟨14712190053778783899486251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808126702519189266324167 14712190053778783899486251)
      ·
        refine ⟨22068285080668175849229377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14712190053778783899486251 22068285080668175849229377)
        ·
          refine ⟨16551213810501131886922033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22068285080668175849229377 16551213810501131886922033)
          ·
            refine ⟨12413410357875848915191525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16551213810501131886922033 12413410357875848915191525)
            ·
              refine ⟨2327514442101721671598411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12413410357875848915191525 2327514442101721671598411)
              ·
                refine ⟨3491271663152582507397617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327514442101721671598411 3491271663152582507397617)
                ·
                  refine ⟨2618453747364436880548213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3491271663152582507397617 2618453747364436880548213)
                  ·
                    refine ⟨245480038815415957551395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2618453747364436880548213 245480038815415957551395)
                    ·
                      rfl

theorem cell23_1434212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1434212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434212 prefixEnd_1434212 := by exact prefixLift 1434212
  have htrace : WordTrace (prefixWord ++ tailWord_1434212) baseStart_1434212 baseEnd_1434212 := by
    simpa [prefixWord, tailWord_1434212, baseEnd_1434212] using wordTrace_append hprefix tailTrace_1434212
  have hstable : (prefixWord ++ tailWord_1434212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434212).length < 2 ^ (prefixWord ++ tailWord_1434212).sum := by decide
  have hdescent : baseEnd_1434212 < baseStart_1434212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434222 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1434222 : Nat := 118140960795 + 1434222 * 2 ^ 59
def prefixEnd_1434222 : Nat := 4983230072969 + 3 ^ 40 * 1434222 * 2
def baseEnd_1434222 : Nat := 736445251252792833529139

theorem tailTrace_1434222 : CollatzResearch.WordTrace tailWord_1434222 prefixEnd_1434222 736445251252792833529139 := by
  unfold tailWord_1434222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538796726258264307699115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34873582540044076307728613 6538796726258264307699115)
  ·
    refine ⟨9808195089387396461548673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6538796726258264307699115 9808195089387396461548673)
    ·
      refine ⟨7356146317040547346161505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9808195089387396461548673 7356146317040547346161505)
      ·
        refine ⟨5517109737780410509621129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7356146317040547346161505 5517109737780410509621129)
        ·
          refine ⟨4137832303335307882215847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5517109737780410509621129 4137832303335307882215847)
          ·
            refine ⟨6206748455002961823323771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137832303335307882215847 6206748455002961823323771)
            ·
              refine ⟨9310122682504442734985657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206748455002961823323771 9310122682504442734985657)
              ·
                refine ⟨6982592011878332051239243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9310122682504442734985657 6982592011878332051239243)
                ·
                  refine ⟨10473888017817498076858865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982592011878332051239243 10473888017817498076858865)
                  ·
                    refine ⟨7855416013363123557644149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10473888017817498076858865 7855416013363123557644149)
                    ·
                      refine ⟨736445251252792833529139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7855416013363123557644149 736445251252792833529139)
                      ·
                        rfl

theorem cell23_1434222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1434222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434222 prefixEnd_1434222 := by exact prefixLift 1434222
  have htrace : WordTrace (prefixWord ++ tailWord_1434222) baseStart_1434222 baseEnd_1434222 := by
    simpa [prefixWord, tailWord_1434222, baseEnd_1434222] using wordTrace_append hprefix tailTrace_1434222
  have hstable : (prefixWord ++ tailWord_1434222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434222).length < 2 ^ (prefixWord ++ tailWord_1434222).sum := by decide
  have hdescent : baseEnd_1434222 < baseStart_1434222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_1434232 : Nat := 118140960795 + 1434232 * 2 ^ 59
def prefixEnd_1434232 : Nat := 4983230072969 + 3 ^ 40 * 1434232 * 2
def baseEnd_1434232 : Nat := 736450386059337794404093

theorem tailTrace_1434232 : CollatzResearch.WordTrace tailWord_1434232 prefixEnd_1434232 736450386059337794404093 := by
  unfold tailWord_1434232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26155369270014943084728475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34873825693353257446304633 26155369270014943084728475)
  ·
    refine ⟨39233053905022414627092713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26155369270014943084728475 39233053905022414627092713)
    ·
      refine ⟨29424790428766810970319535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39233053905022414627092713 29424790428766810970319535)
      ·
        refine ⟨44137185643150216455479303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29424790428766810970319535 44137185643150216455479303)
        ·
          refine ⟨66205778464725324683218955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44137185643150216455479303 66205778464725324683218955)
          ·
            refine ⟨99308667697087987024828433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66205778464725324683218955 99308667697087987024828433)
            ·
              refine ⟨74481500772815990268621325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99308667697087987024828433 74481500772815990268621325)
              ·
                refine ⟨27930562789805996350732997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74481500772815990268621325 27930562789805996350732997)
                ·
                  refine ⟨5236980523088624315762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27930562789805996350732997 5236980523088624315762437)
                  ·
                    refine ⟨981933848079117059205457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236980523088624315762437 981933848079117059205457)
                    ·
                      refine ⟨736450386059337794404093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 981933848079117059205457 736450386059337794404093)
                      ·
                        rfl

theorem cell23_1434232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_1434232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434232 prefixEnd_1434232 := by exact prefixLift 1434232
  have htrace : WordTrace (prefixWord ++ tailWord_1434232) baseStart_1434232 baseEnd_1434232 := by
    simpa [prefixWord, tailWord_1434232, baseEnd_1434232] using wordTrace_append hprefix tailTrace_1434232
  have hstable : (prefixWord ++ tailWord_1434232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434232).length < 2 ^ (prefixWord ++ tailWord_1434232).sum := by decide
  have hdescent : baseEnd_1434232 < baseStart_1434232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434269 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1434269 : Nat := 118140960795 + 1434269 * 2 ^ 59
def prefixEnd_1434269 : Nat := 4983230072969 + 3 ^ 40 * 1434269 * 2
def baseEnd_1434269 : Nat := 736469384843554149641423

theorem tailTrace_1434269 : CollatzResearch.WordTrace tailWord_1434269 prefixEnd_1434269 736469384843554149641423 := by
  unfold tailWord_1434269
  simp only [CollatzResearch.WordTrace]
  refine ⟨52312088040895841488553861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34874725360597227659035907 52312088040895841488553861)
  ·
    refine ⟨9808516507667970279103849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52312088040895841488553861 9808516507667970279103849)
    ·
      refine ⟨7356387380750977709327887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9808516507667970279103849 7356387380750977709327887)
      ·
        refine ⟨11034581071126466563991831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7356387380750977709327887 11034581071126466563991831)
        ·
          refine ⟨16551871606689699845987747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034581071126466563991831 16551871606689699845987747)
          ·
            refine ⟨24827807410034549768981621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16551871606689699845987747 24827807410034549768981621)
            ·
              refine ⟨2327606944690739040842027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24827807410034549768981621 2327606944690739040842027)
              ·
                refine ⟨3491410417036108561263041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327606944690739040842027 3491410417036108561263041)
                ·
                  refine ⟨2618557812777081420947281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3491410417036108561263041 2618557812777081420947281)
                  ·
                    refine ⟨1963918359582811065710461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618557812777081420947281 1963918359582811065710461)
                    ·
                      refine ⟨736469384843554149641423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963918359582811065710461 736469384843554149641423)
                      ·
                        rfl

theorem cell23_1434269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1434269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434269 prefixEnd_1434269 := by exact prefixLift 1434269
  have htrace : WordTrace (prefixWord ++ tailWord_1434269) baseStart_1434269 baseEnd_1434269 := by
    simpa [prefixWord, tailWord_1434269, baseEnd_1434269] using wordTrace_append hprefix tailTrace_1434269
  have hstable : (prefixWord ++ tailWord_1434269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434269).length < 2 ^ (prefixWord ++ tailWord_1434269).sum := by decide
  have hdescent : baseEnd_1434269 < baseStart_1434269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434276 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1434276 : Nat := 118140960795 + 1434276 * 2 ^ 59
def prefixEnd_1434276 : Nat := 4983230072969 + 3 ^ 40 * 1434276 * 2
def baseEnd_1434276 : Nat := 245490993069378540751297

theorem tailTrace_1434276 : CollatzResearch.WordTrace tailWord_1434276 prefixEnd_1434276 245490993069378540751297 := by
  unfold tailWord_1434276
  simp only [CollatzResearch.WordTrace]
  refine ⟨26156171675935240842029341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34874895567913654456039121 26156171675935240842029341)
  ·
    refine ⟨9808564378475715315761003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26156171675935240842029341 9808564378475715315761003)
    ·
      refine ⟨14712846567713572973641505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808564378475715315761003 14712846567713572973641505)
      ·
        refine ⟨11034634925785179730231129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14712846567713572973641505 11034634925785179730231129)
        ·
          refine ⟨8275976194338884797673347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11034634925785179730231129 8275976194338884797673347)
          ·
            refine ⟨12413964291508327196510021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275976194338884797673347 12413964291508327196510021)
            ·
              refine ⟨2327618304657811349345629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12413964291508327196510021 2327618304657811349345629)
              ·
                refine ⟨872856864246679256004611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2327618304657811349345629 872856864246679256004611)
                ·
                  refine ⟨1309285296370018884006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872856864246679256004611 1309285296370018884006917)
                  ·
                    refine ⟨245490993069378540751297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1309285296370018884006917 245490993069378540751297)
                    ·
                      rfl

theorem cell23_1434276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1434276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434276 prefixEnd_1434276 := by exact prefixLift 1434276
  have htrace : WordTrace (prefixWord ++ tailWord_1434276) baseStart_1434276 baseEnd_1434276 := by
    simpa [prefixWord, tailWord_1434276, baseEnd_1434276] using wordTrace_append hprefix tailTrace_1434276
  have hstable : (prefixWord ++ tailWord_1434276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434276).length < 2 ^ (prefixWord ++ tailWord_1434276).sum := by decide
  have hdescent : baseEnd_1434276 < baseStart_1434276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434289 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 8]
def baseStart_1434289 : Nat := 118140960795 + 1434289 * 2 ^ 59
def prefixEnd_1434289 : Nat := 4983230072969 + 3 ^ 40 * 1434289 * 2
def baseEnd_1434289 : Nat := 81831072717404896821259

theorem tailTrace_1434289 : CollatzResearch.WordTrace tailWord_1434289 prefixEnd_1434289 81831072717404896821259 := by
  unfold tailWord_1434289
  simp only [CollatzResearch.WordTrace]
  refine ⟨52312817500823384904281921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34875211667215589936187947 52312817500823384904281921)
  ·
    refine ⟨39234613125617538678211441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52312817500823384904281921 39234613125617538678211441)
    ·
      refine ⟨29425959844213154008658581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39234613125617538678211441 29425959844213154008658581)
      ·
        refine ⟨1379341867697491594155871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29425959844213154008658581 1379341867697491594155871)
        ·
          refine ⟨2069012801546237391233807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379341867697491594155871 2069012801546237391233807)
          ·
            refine ⟨3103519202319356086850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069012801546237391233807 3103519202319356086850711)
            ·
              refine ⟨4655278803479034130276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103519202319356086850711 4655278803479034130276067)
              ·
                refine ⟨6982918205218551195414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655278803479034130276067 6982918205218551195414101)
                ·
                  refine ⟨81831072717404896821259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6982918205218551195414101 81831072717404896821259)
                  ·
                    rfl

theorem cell23_1434289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_1434289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434289 prefixEnd_1434289 := by exact prefixLift 1434289
  have htrace : WordTrace (prefixWord ++ tailWord_1434289) baseStart_1434289 baseEnd_1434289 := by
    simpa [prefixWord, tailWord_1434289, baseEnd_1434289] using wordTrace_append hprefix tailTrace_1434289
  have hstable : (prefixWord ++ tailWord_1434289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434289).length < 2 ^ (prefixWord ++ tailWord_1434289).sum := by decide
  have hdescent : baseEnd_1434289 < baseStart_1434289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434316 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1434316 : Nat := 118140960795 + 1434316 * 2 ^ 59
def prefixEnd_1434316 : Nat := 4983230072969 + 3 ^ 40 * 1434316 * 2
def baseEnd_1434316 : Nat := 736493518434315465753707

theorem tailTrace_1434316 : CollatzResearch.WordTrace tailWord_1434316 prefixEnd_1434316 736493518434315465753707 := by
  unfold tailWord_1434316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26156901135862784257757401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34875868181150379010343201 26156901135862784257757401)
  ·
    refine ⟨19617675851897088193318051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26156901135862784257757401 19617675851897088193318051)
    ·
      refine ⟨29426513777845632289977077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19617675851897088193318051 29426513777845632289977077)
      ·
        refine ⟨2758735666673028027185351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29426513777845632289977077 2758735666673028027185351)
        ·
          refine ⟨4138103500009542040778027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758735666673028027185351 4138103500009542040778027)
          ·
            refine ⟨6207155250014313061167041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138103500009542040778027 6207155250014313061167041)
            ·
              refine ⟨4655366437510734795875281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6207155250014313061167041 4655366437510734795875281)
              ·
                refine ⟨3491524828133051096906461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655366437510734795875281 3491524828133051096906461)
                ·
                  refine ⟨1309321810549894161339923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3491524828133051096906461 1309321810549894161339923)
                  ·
                    refine ⟨1963982715824841242009885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309321810549894161339923 1963982715824841242009885)
                    ·
                      refine ⟨736493518434315465753707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1963982715824841242009885 736493518434315465753707)
                      ·
                        rfl

theorem cell23_1434316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1434316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434316 prefixEnd_1434316 := by exact prefixLift 1434316
  have htrace : WordTrace (prefixWord ++ tailWord_1434316) baseStart_1434316 baseEnd_1434316 := by
    simpa [prefixWord, tailWord_1434316, baseEnd_1434316] using wordTrace_append hprefix tailTrace_1434316
  have hstable : (prefixWord ++ tailWord_1434316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434316).length < 2 ^ (prefixWord ++ tailWord_1434316).sum := by decide
  have hdescent : baseEnd_1434316 < baseStart_1434316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434345 : List Nat := [1, 2, 1, 1, 1, 2, 15]
def baseStart_1434345 : Nat := 118140960795 + 1434345 * 2 ^ 59
def prefixEnd_1434345 : Nat := 4983230072969 + 3 ^ 40 * 1434345 * 2
def baseEnd_1434345 : Nat := 9092696412015998176433

theorem tailTrace_1434345 : CollatzResearch.WordTrace tailWord_1434345 prefixEnd_1434345 9092696412015998176433 := by
  unfold tailWord_1434345
  simp only [CollatzResearch.WordTrace]
  refine ⟨52314859988620506468320489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34876573325747004312213659 52314859988620506468320489)
  ·
    refine ⟨39236144991465379851240367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52314859988620506468320489 39236144991465379851240367)
    ·
      refine ⟨58854217487198069776860551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39236144991465379851240367 58854217487198069776860551)
      ·
        refine ⟨88281326230797104665290827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58854217487198069776860551 88281326230797104665290827)
        ·
          refine ⟨132421989346195656997936241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88281326230797104665290827 132421989346195656997936241)
          ·
            refine ⟨99316492009646742748452181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132421989346195656997936241 99316492009646742748452181)
            ·
              refine ⟨9092696412015998176433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 99316492009646742748452181 9092696412015998176433)
              ·
                rfl

theorem cell23_1434345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 15].length) (baseStart_1434345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434345 prefixEnd_1434345 := by exact prefixLift 1434345
  have htrace : WordTrace (prefixWord ++ tailWord_1434345) baseStart_1434345 baseEnd_1434345 := by
    simpa [prefixWord, tailWord_1434345, baseEnd_1434345] using wordTrace_append hprefix tailTrace_1434345
  have hstable : (prefixWord ++ tailWord_1434345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434345).length < 2 ^ (prefixWord ++ tailWord_1434345).sum := by decide
  have hdescent : baseEnd_1434345 < baseStart_1434345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434349 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1434349 : Nat := 118140960795 + 1434349 * 2 ^ 59
def prefixEnd_1434349 : Nat := 4983230072969 + 3 ^ 40 * 1434349 * 2
def baseEnd_1434349 : Nat := 245503487765304612213685

theorem tailTrace_1434349 : CollatzResearch.WordTrace tailWord_1434349 prefixEnd_1434349 245503487765304612213685 := by
  unfold tailWord_1434349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52315005880606015151466101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34876670587070676767644067 52315005880606015151466101)
  ·
    refine ⟨4904531801306813920449947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52315005880606015151466101 4904531801306813920449947)
    ·
      refine ⟨7356797701960220880674921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904531801306813920449947 7356797701960220880674921)
      ·
        refine ⟨5517598276470165660506191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7356797701960220880674921 5517598276470165660506191)
        ·
          refine ⟨8276397414705248490759287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517598276470165660506191 8276397414705248490759287)
          ·
            refine ⟨12414596122057872736138931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8276397414705248490759287 12414596122057872736138931)
            ·
              refine ⟨18621894183086809104208397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414596122057872736138931 18621894183086809104208397)
              ·
                refine ⟨6983210318657553414078149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18621894183086809104208397 6983210318657553414078149)
                ·
                  refine ⟨1309351934748291265139653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6983210318657553414078149 1309351934748291265139653)
                  ·
                    refine ⟨245503487765304612213685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1309351934748291265139653 245503487765304612213685)
                    ·
                      rfl

theorem cell23_1434349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1434349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434349 prefixEnd_1434349 := by exact prefixLift 1434349
  have htrace : WordTrace (prefixWord ++ tailWord_1434349) baseStart_1434349 baseEnd_1434349 := by
    simpa [prefixWord, tailWord_1434349, baseEnd_1434349] using wordTrace_append hprefix tailTrace_1434349
  have hstable : (prefixWord ++ tailWord_1434349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434349).length < 2 ^ (prefixWord ++ tailWord_1434349).sum := by decide
  have hdescent : baseEnd_1434349 < baseStart_1434349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434350 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_1434350 : Nat := 118140960795 + 1434350 * 2 ^ 59
def prefixEnd_1434350 : Nat := 4983230072969 + 3 ^ 40 * 1434350 * 2
def baseEnd_1434350 : Nat := 736510976776568332728551

theorem tailTrace_1434350 : CollatzResearch.WordTrace tailWord_1434350 prefixEnd_1434350 736510976776568332728551 := by
  unfold tailWord_1434350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539380294200299040281563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34876694902401594881501669 6539380294200299040281563)
  ·
    refine ⟨9809070441300448560422345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6539380294200299040281563 9809070441300448560422345)
    ·
      refine ⟨7356802830975336420316759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9809070441300448560422345 7356802830975336420316759)
      ·
        refine ⟨11035204246463004630475139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7356802830975336420316759 11035204246463004630475139)
        ·
          refine ⟨16552806369694506945712709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035204246463004630475139 16552806369694506945712709)
          ·
            refine ⟨3103651194317720052321133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16552806369694506945712709 3103651194317720052321133)
            ·
              refine ⟨1163869197869145019620425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3103651194317720052321133 1163869197869145019620425)
              ·
                refine ⟨872901898401858764715319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163869197869145019620425 872901898401858764715319)
                ·
                  refine ⟨1309352847602788147072979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872901898401858764715319 1309352847602788147072979)
                  ·
                    refine ⟨1964029271404182220609469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309352847602788147072979 1964029271404182220609469)
                    ·
                      refine ⟨736510976776568332728551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964029271404182220609469 736510976776568332728551)
                      ·
                        rfl

theorem cell23_1434350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_1434350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434350 prefixEnd_1434350 := by exact prefixLift 1434350
  have htrace : WordTrace (prefixWord ++ tailWord_1434350) baseStart_1434350 baseEnd_1434350 := by
    simpa [prefixWord, tailWord_1434350, baseEnd_1434350] using wordTrace_append hprefix tailTrace_1434350
  have hstable : (prefixWord ++ tailWord_1434350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434350).length < 2 ^ (prefixWord ++ tailWord_1434350).sum := by decide
  have hdescent : baseEnd_1434350 < baseStart_1434350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434357 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 6]
def baseStart_1434357 : Nat := 118140960795 + 1434357 * 2 ^ 59
def prefixEnd_1434357 : Nat := 4983230072969 + 3 ^ 40 * 1434357 * 2
def baseEnd_1434357 : Nat := 81834952349016645037891

theorem tailTrace_1434357 : CollatzResearch.WordTrace tailWord_1434357 prefixEnd_1434357 81834952349016645037891 := by
  unfold tailWord_1434357
  simp only [CollatzResearch.WordTrace]
  refine ⟨52315297664577032517757325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34876865109718021678504883 52315297664577032517757325)
  ·
    refine ⟨19618236624216387194158997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52315297664577032517757325 19618236624216387194158997)
    ·
      refine ⟨919604841760143149726203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19618236624216387194158997 919604841760143149726203)
      ·
        refine ⟨1379407262640214724589305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919604841760143149726203 1379407262640214724589305)
        ·
          refine ⟨1034555446980161043441979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379407262640214724589305 1034555446980161043441979)
          ·
            refine ⟨1551833170470241565162969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034555446980161043441979 1551833170470241565162969)
            ·
              refine ⟨1163874877852681173872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551833170470241565162969 1163874877852681173872227)
              ·
                refine ⟨1745812316779021760808341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163874877852681173872227 1745812316779021760808341)
                ·
                  refine ⟨81834952349016645037891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1745812316779021760808341 81834952349016645037891)
                  ·
                    rfl

theorem cell23_1434357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_1434357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434357 prefixEnd_1434357 := by exact prefixLift 1434357
  have htrace : WordTrace (prefixWord ++ tailWord_1434357) baseStart_1434357 baseEnd_1434357 := by
    simpa [prefixWord, tailWord_1434357, baseEnd_1434357] using wordTrace_append hprefix tailTrace_1434357
  have hstable : (prefixWord ++ tailWord_1434357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434357).length < 2 ^ (prefixWord ++ tailWord_1434357).sum := by decide
  have hdescent : baseEnd_1434357 < baseStart_1434357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434376 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_1434376 : Nat := 118140960795 + 1434376 * 2 ^ 59
def prefixEnd_1434376 : Nat := 4983230072969 + 3 ^ 40 * 1434376 * 2
def baseEnd_1434376 : Nat := 736524327273585231003431

theorem tailTrace_1434376 : CollatzResearch.WordTrace tailWord_1434376 prefixEnd_1434376 736524327273585231003431 := by
  unfold tailWord_1434376
  simp only [CollatzResearch.WordTrace]
  refine ⟨26157995325754099381349491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34877327101005465841799321 26157995325754099381349491)
  ·
    refine ⟨39236992988631149072024237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26157995325754099381349491 39236992988631149072024237)
    ·
      refine ⟨14713872370736680902009089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39236992988631149072024237 14713872370736680902009089)
      ·
        refine ⟨11035404278052510676506817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14713872370736680902009089 11035404278052510676506817)
        ·
          refine ⟨8276553208539383007380113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11035404278052510676506817 8276553208539383007380113)
          ·
            refine ⟨6207414906404537255535085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8276553208539383007380113 6207414906404537255535085)
            ·
              refine ⟨2327780589901701470825657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6207414906404537255535085 2327780589901701470825657)
              ·
                refine ⟨1745835442426276103119243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327780589901701470825657 1745835442426276103119243)
                ·
                  refine ⟨2618753163639414154678865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745835442426276103119243 2618753163639414154678865)
                  ·
                    refine ⟨1964064872729560616009149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618753163639414154678865 1964064872729560616009149)
                    ·
                      refine ⟨736524327273585231003431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964064872729560616009149 736524327273585231003431)
                      ·
                        rfl

theorem cell23_1434376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_1434376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434376 prefixEnd_1434376 := by exact prefixLift 1434376
  have htrace : WordTrace (prefixWord ++ tailWord_1434376) baseStart_1434376 baseEnd_1434376 := by
    simpa [prefixWord, tailWord_1434376, baseEnd_1434376] using wordTrace_append hprefix tailTrace_1434376
  have hstable : (prefixWord ++ tailWord_1434376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434376).length < 2 ^ (prefixWord ++ tailWord_1434376).sum := by decide
  have hdescent : baseEnd_1434376 < baseStart_1434376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434389 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1434389 : Nat := 118140960795 + 1434389 * 2 ^ 59
def prefixEnd_1434389 : Nat := 4983230072969 + 3 ^ 40 * 1434389 * 2
def baseEnd_1434389 : Nat := 736531002522093680140871

theorem tailTrace_1434389 : CollatzResearch.WordTrace tailWord_1434389 prefixEnd_1434389 736531002522093680140871 := by
  unfold tailWord_1434389
  simp only [CollatzResearch.WordTrace]
  refine ⟨52316464800461101982922221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34877643200307401321948147 52316464800461101982922221)
  ·
    refine ⟨19618674300172913243595833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52316464800461101982922221 19618674300172913243595833)
    ·
      refine ⟨14714005725129684932696875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19618674300172913243595833 14714005725129684932696875)
      ·
        refine ⟨22071008587694527399045313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14714005725129684932696875 22071008587694527399045313)
        ·
          refine ⟨16553256440770895549283985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22071008587694527399045313 16553256440770895549283985)
          ·
            refine ⟨12414942330578171661962989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16553256440770895549283985 12414942330578171661962989)
            ·
              refine ⟨4655603373966814373236121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12414942330578171661962989 4655603373966814373236121)
              ·
                refine ⟨3491702530475110779927091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655603373966814373236121 3491702530475110779927091)
                ·
                  refine ⟨5237553795712666169890637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491702530475110779927091 5237553795712666169890637)
                  ·
                    refine ⟨1964082673392249813708989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5237553795712666169890637 1964082673392249813708989)
                    ·
                      refine ⟨736531002522093680140871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964082673392249813708989 736531002522093680140871)
                      ·
                        rfl

theorem cell23_1434389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1434389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434389 prefixEnd_1434389 := by exact prefixLift 1434389
  have htrace : WordTrace (prefixWord ++ tailWord_1434389) baseStart_1434389 baseEnd_1434389 := by
    simpa [prefixWord, tailWord_1434389, baseEnd_1434389] using wordTrace_append hprefix tailTrace_1434389
  have hstable : (prefixWord ++ tailWord_1434389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434389).length < 2 ^ (prefixWord ++ tailWord_1434389).sum := by decide
  have hdescent : baseEnd_1434389 < baseStart_1434389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434412 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1434412 : Nat := 118140960795 + 1434412 * 2 ^ 59
def prefixEnd_1434412 : Nat := 4983230072969 + 3 ^ 40 * 1434412 * 2
def baseEnd_1434412 : Nat := 736542812577147090153265

theorem tailTrace_1434412 : CollatzResearch.WordTrace tailWord_1434412 prefixEnd_1434412 736542812577147090153265 := by
  unfold tailWord_1434412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158651839688888455504745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34878202452918517940672993 26158651839688888455504745)
  ·
    refine ⟨19618988879766666341628559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26158651839688888455504745 19618988879766666341628559)
    ·
      refine ⟨29428483319649999512442839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19618988879766666341628559 29428483319649999512442839)
      ·
        refine ⟨44142724979474999268664259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29428483319649999512442839 44142724979474999268664259)
        ·
          refine ⟨66214087469212498902996389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44142724979474999268664259 66214087469212498902996389)
          ·
            refine ⟨12415141400477343544311823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66214087469212498902996389 12415141400477343544311823)
            ·
              refine ⟨18622712100716015316467735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415141400477343544311823 18622712100716015316467735)
              ·
                refine ⟨27934068151074022974701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18622712100716015316467735 27934068151074022974701603)
                ·
                  refine ⟨41901102226611034462052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27934068151074022974701603 41901102226611034462052405)
                  ·
                    refine ⟨3928228333744784480817413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41901102226611034462052405 3928228333744784480817413)
                    ·
                      refine ⟨736542812577147090153265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3928228333744784480817413 736542812577147090153265)
                      ·
                        rfl

theorem cell23_1434412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1434412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434412 prefixEnd_1434412 := by exact prefixLift 1434412
  have htrace : WordTrace (prefixWord ++ tailWord_1434412) baseStart_1434412 baseEnd_1434412 := by
    simpa [prefixWord, tailWord_1434412, baseEnd_1434412] using wordTrace_append hprefix tailTrace_1434412
  have hstable : (prefixWord ++ tailWord_1434412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434412).length < 2 ^ (prefixWord ++ tailWord_1434412).sum := by decide
  have hdescent : baseEnd_1434412 < baseStart_1434412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434413 : List Nat := [1, 5, 3, 2, 1, 2, 1, 8]
def baseStart_1434413 : Nat := 118140960795 + 1434413 * 2 ^ 59
def prefixEnd_1434413 : Nat := 4983230072969 + 3 ^ 40 * 1434413 * 2
def baseEnd_1434413 : Nat := 27279382446585243934843

theorem tailTrace_1434413 : CollatzResearch.WordTrace tailWord_1434413 prefixEnd_1434413 27279382446585243934843 := by
  unfold tailWord_1434413
  simp only [CollatzResearch.WordTrace]
  refine ⟨52317340152374154081795893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34878226768249436054530595 52317340152374154081795893)
  ·
    refine ⟨4904750639285076945168365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52317340152374154081795893 4904750639285076945168365)
    ·
      refine ⟨1839281489731903854438137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4904750639285076945168365 1839281489731903854438137)
      ·
        refine ⟨1379461117298927890828603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839281489731903854438137 1379461117298927890828603)
        ·
          refine ⟨2069191675948391836242905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379461117298927890828603 2069191675948391836242905)
          ·
            refine ⟨1551893756961293877182179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069191675948391836242905 1551893756961293877182179)
            ·
              refine ⟨2327840635441940815773269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551893756961293877182179 2327840635441940815773269)
              ·
                refine ⟨27279382446585243934843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2327840635441940815773269 27279382446585243934843)
                ·
                  rfl

theorem cell23_1434413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 8].length) (baseStart_1434413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434413 prefixEnd_1434413 := by exact prefixLift 1434413
  have htrace : WordTrace (prefixWord ++ tailWord_1434413) baseStart_1434413 baseEnd_1434413 := by
    simpa [prefixWord, tailWord_1434413, baseEnd_1434413] using wordTrace_append hprefix tailTrace_1434413
  have hstable : (prefixWord ++ tailWord_1434413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434413).length < 2 ^ (prefixWord ++ tailWord_1434413).sum := by decide
  have hdescent : baseEnd_1434413 < baseStart_1434413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_1434432 : Nat := 118140960795 + 1434432 * 2 ^ 59
def prefixEnd_1434432 : Nat := 4983230072969 + 3 ^ 40 * 1434432 * 2
def baseEnd_1434432 : Nat := 736553082190237011903173

theorem tailTrace_1434432 : CollatzResearch.WordTrace tailWord_1434432 prefixEnd_1434432 736553082190237011903173 := by
  unfold tailWord_1434432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159016569652660163368775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34878688759536880217825033 26159016569652660163368775)
  ·
    refine ⟨39238524854478990245053163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26159016569652660163368775 39238524854478990245053163)
    ·
      refine ⟨58857787281718485367579745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39238524854478990245053163 58857787281718485367579745)
      ·
        refine ⟨44143340461288864025684809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58857787281718485367579745 44143340461288864025684809)
        ·
          refine ⟨33107505345966648019263607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44143340461288864025684809 33107505345966648019263607)
          ·
            refine ⟨49661258018949972028895411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33107505345966648019263607 49661258018949972028895411)
            ·
              refine ⟨74491887028424958043343117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49661258018949972028895411 74491887028424958043343117)
              ·
                refine ⟨27934457635659359266253669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74491887028424958043343117 27934457635659359266253669)
                ·
                  refine ⟨5237710806686129862422563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27934457635659359266253669 5237710806686129862422563)
                  ·
                    refine ⟨7856566210029194793633845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237710806686129862422563 7856566210029194793633845)
                    ·
                      refine ⟨736553082190237011903173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7856566210029194793633845 736553082190237011903173)
                      ·
                        rfl

theorem cell23_1434432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_1434432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434432 prefixEnd_1434432 := by exact prefixLift 1434432
  have htrace : WordTrace (prefixWord ++ tailWord_1434432) baseStart_1434432 baseEnd_1434432 := by
    simpa [prefixWord, tailWord_1434432, baseEnd_1434432] using wordTrace_append hprefix tailTrace_1434432
  have hstable : (prefixWord ++ tailWord_1434432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434432).length < 2 ^ (prefixWord ++ tailWord_1434432).sum := by decide
  have hdescent : baseEnd_1434432 < baseStart_1434432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434486 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1434486 : Nat := 118140960795 + 1434486 * 2 ^ 59
def prefixEnd_1434486 : Nat := 4983230072969 + 3 ^ 40 * 1434486 * 2
def baseEnd_1434486 : Nat := 81842312238397755625325

theorem tailTrace_1434486 : CollatzResearch.WordTrace tailWord_1434486 prefixEnd_1434486 81842312238397755625325 := by
  unfold tailWord_1434486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270000167569355471825207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34880001787406458366135541 3270000167569355471825207)
  ·
    refine ⟨4905000251354033207737811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3270000167569355471825207 4905000251354033207737811)
    ·
      refine ⟨7357500377031049811606717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905000251354033207737811 7357500377031049811606717)
      ·
        refine ⟨2759062641386643679352519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7357500377031049811606717 2759062641386643679352519)
        ·
          refine ⟨4138593962079965519028779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759062641386643679352519 4138593962079965519028779)
          ·
            refine ⟨6207890943119948278543169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138593962079965519028779 6207890943119948278543169)
            ·
              refine ⟨4655918207339961208907377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6207890943119948278543169 4655918207339961208907377)
              ·
                refine ⟨3491938655504970906680533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655918207339961208907377 3491938655504970906680533)
                ·
                  refine ⟨81842312238397755625325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3491938655504970906680533 81842312238397755625325)
                  ·
                    rfl

theorem cell23_1434486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1434486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434486 prefixEnd_1434486 := by exact prefixLift 1434486
  have htrace : WordTrace (prefixWord ++ tailWord_1434486) baseStart_1434486 baseEnd_1434486 := by
    simpa [prefixWord, tailWord_1434486, baseEnd_1434486] using wordTrace_append hprefix tailTrace_1434486
  have hstable : (prefixWord ++ tailWord_1434486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434486).length < 2 ^ (prefixWord ++ tailWord_1434486).sum := by decide
  have hdescent : baseEnd_1434486 < baseStart_1434486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434499 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 2, 5]
def baseStart_1434499 : Nat := 118140960795 + 1434499 * 2 ^ 59
def prefixEnd_1434499 : Nat := 4983230072969 + 3 ^ 40 * 1434499 * 2
def baseEnd_1434499 : Nat := 245529161798029416588455

theorem tailTrace_1434499 : CollatzResearch.WordTrace tailWord_1434499 prefixEnd_1434499 245529161798029416588455 := by
  unfold tailWord_1434499
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320476830062590769426551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34880317886708393846284367 52320476830062590769426551)
  ·
    refine ⟨78480715245093886154139827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52320476830062590769426551 78480715245093886154139827)
    ·
      refine ⟨117721072867640829231209741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78480715245093886154139827 117721072867640829231209741)
      ·
        refine ⟨44145402325365310961703653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117721072867640829231209741 44145402325365310961703653)
        ·
          refine ⟨8277262936005995805319435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44145402325365310961703653 8277262936005995805319435)
          ·
            refine ⟨12415894404008993707979153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8277262936005995805319435 12415894404008993707979153)
            ·
              refine ⟨9311920803006745280984365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12415894404008993707979153 9311920803006745280984365)
              ·
                refine ⟨3491970301127529480369137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9311920803006745280984365 3491970301127529480369137)
                ·
                  refine ⟨2618977725845647110276853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3491970301127529480369137 2618977725845647110276853)
                  ·
                    refine ⟨245529161798029416588455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2618977725845647110276853 245529161798029416588455)
                    ·
                      rfl

theorem cell23_1434499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].length) (baseStart_1434499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434499 prefixEnd_1434499 := by exact prefixLift 1434499
  have htrace : WordTrace (prefixWord ++ tailWord_1434499) baseStart_1434499 baseEnd_1434499 := by
    simpa [prefixWord, tailWord_1434499, baseEnd_1434499] using wordTrace_append hprefix tailTrace_1434499
  have hstable : (prefixWord ++ tailWord_1434499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434499).length < 2 ^ (prefixWord ++ tailWord_1434499).sum := by decide
  have hdescent : baseEnd_1434499 < baseStart_1434499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434503 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 5]
def baseStart_1434503 : Nat := 118140960795 + 1434503 * 2 ^ 59
def prefixEnd_1434503 : Nat := 4983230072969 + 3 ^ 40 * 1434503 * 2
def baseEnd_1434503 : Nat := 81843282146300692679483

theorem tailTrace_1434503 : CollatzResearch.WordTrace tailWord_1434503 prefixEnd_1434503 81843282146300692679483 := by
  unfold tailWord_1434503
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320622722048099452572163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34880415148032066301714775 52320622722048099452572163)
  ·
    refine ⟨78480934083072149178858245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52320622722048099452572163 78480934083072149178858245)
    ·
      refine ⟨14715175140576027971035921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78480934083072149178858245 14715175140576027971035921)
      ·
        refine ⟨11036381355432020978276941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14715175140576027971035921 11036381355432020978276941)
        ·
          refine ⟨4138643008287007866853853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11036381355432020978276941 4138643008287007866853853)
          ·
            refine ⟨1551991128107627950070195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4138643008287007866853853 1551991128107627950070195)
            ·
              refine ⟨2327986692161441925105293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551991128107627950070195 2327986692161441925105293)
              ·
                refine ⟨872995009560540721914485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2327986692161441925105293 872995009560540721914485)
                ·
                  refine ⟨81843282146300692679483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872995009560540721914485 81843282146300692679483)
                  ·
                    rfl

theorem cell23_1434503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 5].length) (baseStart_1434503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434503 prefixEnd_1434503 := by exact prefixLift 1434503
  have htrace : WordTrace (prefixWord ++ tailWord_1434503) baseStart_1434503 baseEnd_1434503 := by
    simpa [prefixWord, tailWord_1434503, baseEnd_1434503] using wordTrace_append hprefix tailTrace_1434503
  have hstable : (prefixWord ++ tailWord_1434503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434503).length < 2 ^ (prefixWord ++ tailWord_1434503).sum := by decide
  have hdescent : baseEnd_1434503 < baseStart_1434503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434512 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_1434512 : Nat := 118140960795 + 1434512 * 2 ^ 59
def prefixEnd_1434512 : Nat := 4983230072969 + 3 ^ 40 * 1434512 * 2
def baseEnd_1434512 : Nat := 245531386880865566300935

theorem tailTrace_1434512 : CollatzResearch.WordTrace tailWord_1434512 prefixEnd_1434512 245531386880865566300935 := by
  unfold tailWord_1434512
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160475489507746994824895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34880633986010329326433193 26160475489507746994824895)
  ·
    refine ⟨39240713234261620492237343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26160475489507746994824895 39240713234261620492237343)
    ·
      refine ⟨58861069851392430738356015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39240713234261620492237343 58861069851392430738356015)
      ·
        refine ⟨88291604777088646107534023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58861069851392430738356015 88291604777088646107534023)
        ·
          refine ⟨132437407165632969161301035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88291604777088646107534023 132437407165632969161301035)
          ·
            refine ⟨198656110748449453741951553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132437407165632969161301035 198656110748449453741951553)
            ·
              refine ⟨148992083061337090306463665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198656110748449453741951553 148992083061337090306463665)
              ·
                refine ⟨111744062296002817729847749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148992083061337090306463665 111744062296002817729847749)
                ·
                  refine ⟨20952011680500528324346453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111744062296002817729847749 20952011680500528324346453)
                  ·
                    refine ⟨245531386880865566300935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20952011680500528324346453 245531386880865566300935)
                    ·
                      rfl

theorem cell23_1434512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_1434512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434512 prefixEnd_1434512 := by exact prefixLift 1434512
  have htrace : WordTrace (prefixWord ++ tailWord_1434512) baseStart_1434512 baseEnd_1434512 := by
    simpa [prefixWord, tailWord_1434512, baseEnd_1434512] using wordTrace_append hprefix tailTrace_1434512
  have hstable : (prefixWord ++ tailWord_1434512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434512).length < 2 ^ (prefixWord ++ tailWord_1434512).sum := by decide
  have hdescent : baseEnd_1434512 < baseStart_1434512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434516 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1434516 : Nat := 118140960795 + 1434516 * 2 ^ 59
def prefixEnd_1434516 : Nat := 4983230072969 + 3 ^ 40 * 1434516 * 2
def baseEnd_1434516 : Nat := 245532071521738227750929

theorem tailTrace_1434516 : CollatzResearch.WordTrace tailWord_1434516 prefixEnd_1434516 245532071521738227750929 := by
  unfold tailWord_1434516
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160548435500501336397701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34880731247334001781863601 26160548435500501336397701)
  ·
    refine ⟨4905102831656344000574569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26160548435500501336397701 4905102831656344000574569)
    ·
      refine ⟨3678827123742258000430927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4905102831656344000574569 3678827123742258000430927)
      ·
        refine ⟨5518240685613387000646391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678827123742258000430927 5518240685613387000646391)
        ·
          refine ⟨8277361028420080500969587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518240685613387000646391 8277361028420080500969587)
          ·
            refine ⟨12416041542630120751454381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8277361028420080500969587 12416041542630120751454381)
            ·
              refine ⟨4656015578486295281795393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12416041542630120751454381 4656015578486295281795393)
              ·
                refine ⟨3492011683864721461346545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656015578486295281795393 3492011683864721461346545)
                ·
                  refine ⟨2619008762898541096009909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492011683864721461346545 2619008762898541096009909)
                  ·
                    refine ⟨245532071521738227750929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2619008762898541096009909 245532071521738227750929)
                    ·
                      rfl

theorem cell23_1434516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1434516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434516 prefixEnd_1434516 := by exact prefixLift 1434516
  have htrace : WordTrace (prefixWord ++ tailWord_1434516) baseStart_1434516 baseEnd_1434516 := by
    simpa [prefixWord, tailWord_1434516, baseEnd_1434516] using wordTrace_append hprefix tailTrace_1434516
  have hstable : (prefixWord ++ tailWord_1434516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434516).length < 2 ^ (prefixWord ++ tailWord_1434516).sum := by decide
  have hdescent : baseEnd_1434516 < baseStart_1434516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434580 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1434580 : Nat := 118140960795 + 1434580 * 2 ^ 59
def prefixEnd_1434580 : Nat := 4983230072969 + 3 ^ 40 * 1434580 * 2
def baseEnd_1434580 : Nat := 245543025775700810950831

theorem tailTrace_1434580 : CollatzResearch.WordTrace tailWord_1434580 prefixEnd_1434580 245543025775700810950831 := by
  unfold tailWord_1434580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161715571384570801562597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34882287428512761068750129 26161715571384570801562597)
  ·
    refine ⟨4905321669634607025292987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26161715571384570801562597 4905321669634607025292987)
    ·
      refine ⟨7357982504451910537939481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905321669634607025292987 7357982504451910537939481)
      ·
        refine ⟨5518486878338932903454611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357982504451910537939481 5518486878338932903454611)
        ·
          refine ⟨8277730317508399355181917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518486878338932903454611 8277730317508399355181917)
          ·
            refine ⟨3104148869065649758193219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8277730317508399355181917 3104148869065649758193219)
            ·
              refine ⟨4656223303598474637289829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104148869065649758193219 4656223303598474637289829)
              ·
                refine ⟨873041869424713994491843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4656223303598474637289829 873041869424713994491843)
                ·
                  refine ⟨1309562804137070991737765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873041869424713994491843 1309562804137070991737765)
                  ·
                    refine ⟨245543025775700810950831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1309562804137070991737765 245543025775700810950831)
                    ·
                      rfl

theorem cell23_1434580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1434580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434580 prefixEnd_1434580 := by exact prefixLift 1434580
  have htrace : WordTrace (prefixWord ++ tailWord_1434580) baseStart_1434580 baseEnd_1434580 := by
    simpa [prefixWord, tailWord_1434580, baseEnd_1434580] using wordTrace_append hprefix tailTrace_1434580
  have hstable : (prefixWord ++ tailWord_1434580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434580).length < 2 ^ (prefixWord ++ tailWord_1434580).sum := by decide
  have hdescent : baseEnd_1434580 < baseStart_1434580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434620 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_1434620 : Nat := 118140960795 + 1434620 * 2 ^ 59
def prefixEnd_1434620 : Nat := 4983230072969 + 3 ^ 40 * 1434620 * 2
def baseEnd_1434620 : Nat := 736649616553282276352309

theorem tailTrace_1434620 : CollatzResearch.WordTrace tailWord_1434620 prefixEnd_1434620 736649616553282276352309 := by
  unfold tailWord_1434620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162445031312114217290657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34883260041749485623054209 26162445031312114217290657)
  ·
    refine ⟨19621833773484085662967993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26162445031312114217290657 19621833773484085662967993)
    ·
      refine ⟨14716375330113064247225995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19621833773484085662967993 14716375330113064247225995)
      ·
        refine ⟨22074562995169596370838993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716375330113064247225995 22074562995169596370838993)
        ·
          refine ⟨16555922246377197278129245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074562995169596370838993 16555922246377197278129245)
          ·
            refine ⟨6208470842391448979298467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16555922246377197278129245 6208470842391448979298467)
            ·
              refine ⟨9312706263587173468947701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208470842391448979298467 9312706263587173468947701)
              ·
                refine ⟨873066212211297512713847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9312706263587173468947701 873066212211297512713847)
                ·
                  refine ⟨1309599318316946269070771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873066212211297512713847 1309599318316946269070771)
                  ·
                    refine ⟨1964398977475419403606157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309599318316946269070771 1964398977475419403606157)
                    ·
                      refine ⟨736649616553282276352309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964398977475419403606157 736649616553282276352309)
                      ·
                        rfl

theorem cell23_1434620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_1434620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434620 prefixEnd_1434620 := by exact prefixLift 1434620
  have htrace : WordTrace (prefixWord ++ tailWord_1434620) baseStart_1434620 baseEnd_1434620 := by
    simpa [prefixWord, tailWord_1434620, baseEnd_1434620] using wordTrace_append hprefix tailTrace_1434620
  have hstable : (prefixWord ++ tailWord_1434620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434620).length < 2 ^ (prefixWord ++ tailWord_1434620).sum := by decide
  have hdescent : baseEnd_1434620 < baseStart_1434620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434660 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1434660 : Nat := 118140960795 + 1434660 * 2 ^ 59
def prefixEnd_1434660 : Nat := 4983230072969 + 3 ^ 40 * 1434660 * 2
def baseEnd_1434660 : Nat := 736670155779462119852125

theorem tailTrace_1434660 : CollatzResearch.WordTrace tailWord_1434660 prefixEnd_1434660 736670155779462119852125 := by
  unfold tailWord_1434660
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163174491239657633018717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34884232654986210177358289 26163174491239657633018717)
  ·
    refine ⟨9811190434214871612382019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26163174491239657633018717 9811190434214871612382019)
    ·
      refine ⟨14716785651322307418573029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811190434214871612382019 14716785651322307418573029)
      ·
        refine ⟨2759397309622932640982443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14716785651322307418573029 2759397309622932640982443)
        ·
          refine ⟨4139095964434398961473665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759397309622932640982443 4139095964434398961473665)
          ·
            refine ⟨3104321973325799221105249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4139095964434398961473665 3104321973325799221105249)
            ·
              refine ⟨2328241479994349415828937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104321973325799221105249 2328241479994349415828937)
              ·
                refine ⟨1746181109995762061871703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328241479994349415828937 1746181109995762061871703)
                ·
                  refine ⟨2619271664993643092807555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746181109995762061871703 2619271664993643092807555)
                  ·
                    refine ⟨3928907497490464639211333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619271664993643092807555 3928907497490464639211333)
                    ·
                      refine ⟨736670155779462119852125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3928907497490464639211333 736670155779462119852125)
                      ·
                        rfl

theorem cell23_1434660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1434660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434660 prefixEnd_1434660 := by exact prefixLift 1434660
  have htrace : WordTrace (prefixWord ++ tailWord_1434660) baseStart_1434660 baseEnd_1434660 := by
    simpa [prefixWord, tailWord_1434660, baseEnd_1434660] using wordTrace_append hprefix tailTrace_1434660
  have hstable : (prefixWord ++ tailWord_1434660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434660).length < 2 ^ (prefixWord ++ tailWord_1434660).sum := by decide
  have hdescent : baseEnd_1434660 < baseStart_1434660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434679 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1434679 : Nat := 118140960795 + 1434679 * 2 ^ 59
def prefixEnd_1434679 : Nat := 4983230072969 + 3 ^ 40 * 1434679 * 2
def baseEnd_1434679 : Nat := 245559970637299181838179

theorem tailTrace_1434679 : CollatzResearch.WordTrace tailWord_1434679 prefixEnd_1434679 245559970637299181838179 := by
  unfold tailWord_1434679
  simp only [CollatzResearch.WordTrace]
  refine ⟨52327041969410481510979091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34884694646273654340652727 52327041969410481510979091)
  ·
    refine ⟨78490562954115722266468637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52327041969410481510979091 78490562954115722266468637)
    ·
      refine ⟨29433961107793395849925739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78490562954115722266468637 29433961107793395849925739)
      ·
        refine ⟨44150941661690093774888609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29433961107793395849925739 44150941661690093774888609)
        ·
          refine ⟨33113206246267570331166457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44150941661690093774888609 33113206246267570331166457)
          ·
            refine ⟨24834904684700677748374843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33113206246267570331166457 24834904684700677748374843)
            ·
              refine ⟨37252357027051016622562265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24834904684700677748374843 37252357027051016622562265)
              ·
                refine ⟨27939267770288262466921699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37252357027051016622562265 27939267770288262466921699)
                ·
                  refine ⟨41908901655432393700382549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27939267770288262466921699 41908901655432393700382549)
                  ·
                    refine ⟨245559970637299181838179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 41908901655432393700382549 245559970637299181838179)
                    ·
                      rfl

theorem cell23_1434679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1434679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434679 prefixEnd_1434679 := by exact prefixLift 1434679
  have htrace : WordTrace (prefixWord ++ tailWord_1434679) baseStart_1434679 baseEnd_1434679 := by
    simpa [prefixWord, tailWord_1434679, baseEnd_1434679] using wordTrace_append hprefix tailTrace_1434679
  have hstable : (prefixWord ++ tailWord_1434679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434679).length < 2 ^ (prefixWord ++ tailWord_1434679).sum := by decide
  have hdescent : baseEnd_1434679 < baseStart_1434679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434693 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_1434693 : Nat := 118140960795 + 1434693 * 2 ^ 59
def prefixEnd_1434693 : Nat := 4983230072969 + 3 ^ 40 * 1434693 * 2
def baseEnd_1434693 : Nat := 736687100641060490739473

theorem tailTrace_1434693 : CollatzResearch.WordTrace tailWord_1434693 prefixEnd_1434693 736687100641060490739473 := by
  unfold tailWord_1434693
  simp only [CollatzResearch.WordTrace]
  refine ⟨52327552591359761901988733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34885035060906507934659155 52327552591359761901988733)
  ·
    refine ⟨19622832221759910713245775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52327552591359761901988733 19622832221759910713245775)
    ·
      refine ⟨29434248332639866069868663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622832221759910713245775 29434248332639866069868663)
      ·
        refine ⟨44151372498959799104802995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29434248332639866069868663 44151372498959799104802995)
        ·
          refine ⟨66227058748439698657204493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44151372498959799104802995 66227058748439698657204493)
          ·
            refine ⟨24835147030664886996451685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66227058748439698657204493 24835147030664886996451685)
            ·
              refine ⟨4656590068249666311834691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24835147030664886996451685 4656590068249666311834691)
              ·
                refine ⟨6984885102374499467752037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656590068249666311834691 6984885102374499467752037)
                ·
                  refine ⟨1309665956695218650203507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6984885102374499467752037 1309665956695218650203507)
                  ·
                    refine ⟨1964498935042827975305261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309665956695218650203507 1964498935042827975305261)
                    ·
                      refine ⟨736687100641060490739473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964498935042827975305261 736687100641060490739473)
                      ·
                        rfl

theorem cell23_1434693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_1434693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434693 prefixEnd_1434693 := by exact prefixLift 1434693
  have htrace : WordTrace (prefixWord ++ tailWord_1434693) baseStart_1434693 baseEnd_1434693 := by
    simpa [prefixWord, tailWord_1434693, baseEnd_1434693] using wordTrace_append hprefix tailTrace_1434693
  have hstable : (prefixWord ++ tailWord_1434693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434693).length < 2 ^ (prefixWord ++ tailWord_1434693).sum := by decide
  have hdescent : baseEnd_1434693 < baseStart_1434693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434694 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1434694 : Nat := 118140960795 + 1434694 * 2 ^ 59
def prefixEnd_1434694 : Nat := 4983230072969 + 3 ^ 40 * 1434694 * 2
def baseEnd_1434694 : Nat := 736687614121714986826969

theorem tailTrace_1434694 : CollatzResearch.WordTrace tailWord_1434694 prefixEnd_1434694 736687614121714986826969 := by
  unfold tailWord_1434694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635237158261129346024223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34885059376237426048516757 1635237158261129346024223)
  ·
    refine ⟨2452855737391694019036335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1635237158261129346024223 2452855737391694019036335)
    ·
      refine ⟨3679283606087541028554503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452855737391694019036335 3679283606087541028554503)
      ·
        refine ⟨5518925409131311542831755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679283606087541028554503 5518925409131311542831755)
        ·
          refine ⟨8278388113696967314247633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518925409131311542831755 8278388113696967314247633)
          ·
            refine ⟨6208791085272725485685725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8278388113696967314247633 6208791085272725485685725)
            ·
              refine ⟨2328296656977272057132147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6208791085272725485685725 2328296656977272057132147)
              ·
                refine ⟨3492444985465908085698221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328296656977272057132147 3492444985465908085698221)
                ·
                  refine ⟨1309666869549715532136833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3492444985465908085698221 1309666869549715532136833)
                  ·
                    refine ⟨982250152162286649102625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1309666869549715532136833 982250152162286649102625)
                    ·
                      refine ⟨736687614121714986826969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982250152162286649102625 736687614121714986826969)
                      ·
                        rfl

theorem cell23_1434694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1434694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434694 prefixEnd_1434694 := by exact prefixLift 1434694
  have htrace : WordTrace (prefixWord ++ tailWord_1434694) baseStart_1434694 baseEnd_1434694 := by
    simpa [prefixWord, tailWord_1434694, baseEnd_1434694] using wordTrace_append hprefix tailTrace_1434694
  have hstable : (prefixWord ++ tailWord_1434694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434694).length < 2 ^ (prefixWord ++ tailWord_1434694).sum := by decide
  have hdescent : baseEnd_1434694 < baseStart_1434694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434736 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_1434736 : Nat := 118140960795 + 1434736 * 2 ^ 59
def prefixEnd_1434736 : Nat := 4983230072969 + 3 ^ 40 * 1434736 * 2
def baseEnd_1434736 : Nat := 736709180309203822501775

theorem tailTrace_1434736 : CollatzResearch.WordTrace tailWord_1434736 prefixEnd_1434736 736709180309203822501775 := by
  unfold tailWord_1434736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26164560465101990122902031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34886080620135986830536041 26164560465101990122902031)
  ·
    refine ⟨39246840697652985184353047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26164560465101990122902031 39246840697652985184353047)
    ·
      refine ⟨58870261046479477776529571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39246840697652985184353047 58870261046479477776529571)
      ·
        refine ⟨88305391569719216664794357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58870261046479477776529571 88305391569719216664794357)
        ·
          refine ⟨8278630459661176562324471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88305391569719216664794357 8278630459661176562324471)
          ·
            refine ⟨12417945689491764843486707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278630459661176562324471 12417945689491764843486707)
            ·
              refine ⟨18626918534237647265230061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417945689491764843486707 18626918534237647265230061)
              ·
                refine ⟨6985094450339117724461273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18626918534237647265230061 6985094450339117724461273)
                ·
                  refine ⟨5238820837754338293345955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985094450339117724461273 5238820837754338293345955)
                  ·
                    refine ⟨7858231256631507440018933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238820837754338293345955 7858231256631507440018933)
                    ·
                      refine ⟨736709180309203822501775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7858231256631507440018933 736709180309203822501775)
                      ·
                        rfl

theorem cell23_1434736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_1434736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434736 prefixEnd_1434736 := by exact prefixLift 1434736
  have htrace : WordTrace (prefixWord ++ tailWord_1434736) baseStart_1434736 baseEnd_1434736 := by
    simpa [prefixWord, tailWord_1434736, baseEnd_1434736] using wordTrace_append hprefix tailTrace_1434736
  have hstable : (prefixWord ++ tailWord_1434736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434736).length < 2 ^ (prefixWord ++ tailWord_1434736).sum := by decide
  have hdescent : baseEnd_1434736 < baseStart_1434736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434753 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1434753 : Nat := 118140960795 + 1434753 * 2 ^ 59
def prefixEnd_1434753 : Nat := 4983230072969 + 3 ^ 40 * 1434753 * 2
def baseEnd_1434753 : Nat := 736717909480330255989197

theorem tailTrace_1434753 : CollatzResearch.WordTrace tailWord_1434753 prefixEnd_1434753 736717909480330255989197 := by
  unfold tailWord_1434753
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329740971142392149172913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34886493980761594766115275 52329740971142392149172913)
  ·
    refine ⟨39247305728356794111879685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52329740971142392149172913 39247305728356794111879685)
    ·
      refine ⟨7358869824066898895977441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39247305728356794111879685 7358869824066898895977441)
      ·
        refine ⟨5519152368050174171983081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7358869824066898895977441 5519152368050174171983081)
        ·
          refine ⟨4139364276037630628987311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519152368050174171983081 4139364276037630628987311)
          ·
            refine ⟨6209046414056445943480967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139364276037630628987311 6209046414056445943480967)
            ·
              refine ⟨9313569621084668915221451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209046414056445943480967 9313569621084668915221451)
              ·
                refine ⟨13970354431627003372832177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313569621084668915221451 13970354431627003372832177)
                ·
                  refine ⟨10477765823720252529624133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13970354431627003372832177 10477765823720252529624133)
                  ·
                    refine ⟨1964581091947547349304525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10477765823720252529624133 1964581091947547349304525)
                    ·
                      refine ⟨736717909480330255989197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964581091947547349304525 736717909480330255989197)
                      ·
                        rfl

theorem cell23_1434753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1434753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434753 prefixEnd_1434753 := by exact prefixLift 1434753
  have htrace : WordTrace (prefixWord ++ tailWord_1434753) baseStart_1434753 baseEnd_1434753 := by
    simpa [prefixWord, tailWord_1434753, baseEnd_1434753] using wordTrace_append hprefix tailTrace_1434753
  have hstable : (prefixWord ++ tailWord_1434753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434753).length < 2 ^ (prefixWord ++ tailWord_1434753).sum := by decide
  have hdescent : baseEnd_1434753 < baseStart_1434753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434796 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1434796 : Nat := 118140960795 + 1434796 * 2 ^ 59
def prefixEnd_1434796 : Nat := 4983230072969 + 3 ^ 40 * 1434796 * 2
def baseEnd_1434796 : Nat := 736739989148473587751499

theorem tailTrace_1434796 : CollatzResearch.WordTrace tailWord_1434796 prefixEnd_1434796 736739989148473587751499 := by
  unfold tailWord_1434796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165654654993305246494121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34887539539991073661992161 26165654654993305246494121)
  ·
    refine ⟨19624240991244978934870591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26165654654993305246494121 19624240991244978934870591)
    ·
      refine ⟨29436361486867468402305887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19624240991244978934870591 29436361486867468402305887)
      ·
        refine ⟨44154542230301202603458831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29436361486867468402305887 44154542230301202603458831)
        ·
          refine ⟨66231813345451803905188247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44154542230301202603458831 66231813345451803905188247)
          ·
            refine ⟨99347720018177705857782371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66231813345451803905188247 99347720018177705857782371)
            ·
              refine ⟨149021580027266558786673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99347720018177705857782371 149021580027266558786673557)
              ·
                refine ⟨6985386563778119943125323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149021580027266558786673557 6985386563778119943125323)
                ·
                  refine ⟨10478079845667179914687985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985386563778119943125323 10478079845667179914687985)
                  ·
                    refine ⟨7858559884250384936015989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10478079845667179914687985 7858559884250384936015989)
                    ·
                      refine ⟨736739989148473587751499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7858559884250384936015989 736739989148473587751499)
                      ·
                        rfl

theorem cell23_1434796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1434796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434796 prefixEnd_1434796 := by exact prefixLift 1434796
  have htrace : WordTrace (prefixWord ++ tailWord_1434796) baseStart_1434796 baseEnd_1434796 := by
    simpa [prefixWord, tailWord_1434796, baseEnd_1434796] using wordTrace_append hprefix tailTrace_1434796
  have hstable : (prefixWord ++ tailWord_1434796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434796).length < 2 ^ (prefixWord ++ tailWord_1434796).sum := by decide
  have hdescent : baseEnd_1434796 < baseStart_1434796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434818 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1434818 : Nat := 118140960795 + 1434818 * 2 ^ 59
def prefixEnd_1434818 : Nat := 4983230072969 + 3 ^ 40 * 1434818 * 2
def baseEnd_1434818 : Nat := 736751285722872501676399

theorem tailTrace_1434818 : CollatzResearch.WordTrace tailWord_1434818 prefixEnd_1434818 736751285722872501676399 := by
  unfold tailWord_1434818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083027928976727062572277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34888074477271272166859405 13083027928976727062572277)
  ·
    refine ⟨1226533868341568162116151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13083027928976727062572277 1226533868341568162116151)
    ·
      refine ⟨1839800802512352243174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226533868341568162116151 1839800802512352243174227)
      ·
        refine ⟨2759701203768528364761341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839800802512352243174227 2759701203768528364761341)
        ·
          refine ⟨1034887951413198136785503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2759701203768528364761341 1034887951413198136785503)
          ·
            refine ⟨1552331927119797205178255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034887951413198136785503 1552331927119797205178255)
            ·
              refine ⟨2328497890679695807767383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552331927119797205178255 2328497890679695807767383)
              ·
                refine ⟨3492746836019543711651075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328497890679695807767383 3492746836019543711651075)
                ·
                  refine ⟨5239120254029315567476613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492746836019543711651075 5239120254029315567476613)
                  ·
                    refine ⟨982335047630496668901865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239120254029315567476613 982335047630496668901865)
                    ·
                      refine ⟨736751285722872501676399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982335047630496668901865 736751285722872501676399)
                      ·
                        rfl

theorem cell23_1434818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1434818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434818 prefixEnd_1434818 := by exact prefixLift 1434818
  have htrace : WordTrace (prefixWord ++ tailWord_1434818) baseStart_1434818 baseEnd_1434818 := by
    simpa [prefixWord, tailWord_1434818, baseEnd_1434818] using wordTrace_append hprefix tailTrace_1434818
  have hstable : (prefixWord ++ tailWord_1434818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434818).length < 2 ^ (prefixWord ++ tailWord_1434818).sum := by decide
  have hdescent : baseEnd_1434818 < baseStart_1434818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434860 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_1434860 : Nat := 118140960795 + 1434860 * 2 ^ 59
def prefixEnd_1434860 : Nat := 4983230072969 + 3 ^ 40 * 1434860 * 2
def baseEnd_1434860 : Nat := 736772851910361337351205

theorem tailTrace_1434860 : CollatzResearch.WordTrace tailWord_1434860 prefixEnd_1434860 736772851910361337351205 := by
  unfold tailWord_1434860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26166821790877374711659017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34889095721169832948878689 26166821790877374711659017)
  ·
    refine ⟨19625116343158031033744263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26166821790877374711659017 19625116343158031033744263)
    ·
      refine ⟨29437674514737046550616395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19625116343158031033744263 29437674514737046550616395)
      ·
        refine ⟨44156511772105569825924593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29437674514737046550616395 44156511772105569825924593)
        ·
          refine ⟨33117383829079177369443445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44156511772105569825924593 33117383829079177369443445)
          ·
            refine ⟨3104754733976172878385323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33117383829079177369443445 3104754733976172878385323)
            ·
              refine ⟨4657132100964259317577985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104754733976172878385323 4657132100964259317577985)
              ·
                refine ⟨3492849075723194488183489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657132100964259317577985 3492849075723194488183489)
                ·
                  refine ⟨2619636806792395866137617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492849075723194488183489 2619636806792395866137617)
                  ·
                    refine ⟨1964727605094296899603213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2619636806792395866137617 1964727605094296899603213)
                    ·
                      refine ⟨736772851910361337351205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964727605094296899603213 736772851910361337351205)
                      ·
                        rfl

theorem cell23_1434860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_1434860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434860 prefixEnd_1434860 := by exact prefixLift 1434860
  have htrace : WordTrace (prefixWord ++ tailWord_1434860) baseStart_1434860 baseEnd_1434860 := by
    simpa [prefixWord, tailWord_1434860, baseEnd_1434860] using wordTrace_append hprefix tailTrace_1434860
  have hstable : (prefixWord ++ tailWord_1434860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434860).length < 2 ^ (prefixWord ++ tailWord_1434860).sum := by decide
  have hdescent : baseEnd_1434860 < baseStart_1434860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434890 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1434890 : Nat := 118140960795 + 1434890 * 2 ^ 59
def prefixEnd_1434890 : Nat := 4983230072969 + 3 ^ 40 * 1434890 * 2
def baseEnd_1434890 : Nat := 736788256329996219976067

theorem tailTrace_1434890 : CollatzResearch.WordTrace tailWord_1434890 prefixEnd_1434890 736788256329996219976067 := by
  unfold tailWord_1434890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083684442911516136727531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34889825181097376364606749 13083684442911516136727531)
  ·
    refine ⟨19625526664367274205091297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13083684442911516136727531 19625526664367274205091297)
    ·
      refine ⟨14719144998275455653818473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19625526664367274205091297 14719144998275455653818473)
      ·
        refine ⟨11039358748706591740363855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14719144998275455653818473 11039358748706591740363855)
        ·
          refine ⟨16559038123059887610545783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039358748706591740363855 16559038123059887610545783)
          ·
            refine ⟨24838557184589831415818675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16559038123059887610545783 24838557184589831415818675)
            ·
              refine ⟨37257835776884747123728013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24838557184589831415818675 37257835776884747123728013)
              ·
                refine ⟨13971688416331780171398005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37257835776884747123728013 13971688416331780171398005)
                ·
                  refine ⟨1309845789031104391068563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13971688416331780171398005 1309845789031104391068563)
                  ·
                    refine ⟨1964768683546656586602845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309845789031104391068563 1964768683546656586602845)
                    ·
                      refine ⟨736788256329996219976067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964768683546656586602845 736788256329996219976067)
                      ·
                        rfl

theorem cell23_1434890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1434890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434890 prefixEnd_1434890 := by exact prefixLift 1434890
  have htrace : WordTrace (prefixWord ++ tailWord_1434890) baseStart_1434890 baseEnd_1434890 := by
    simpa [prefixWord, tailWord_1434890, baseEnd_1434890] using wordTrace_append hprefix tailTrace_1434890
  have hstable : (prefixWord ++ tailWord_1434890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434890).length < 2 ^ (prefixWord ++ tailWord_1434890).sum := by decide
  have hdescent : baseEnd_1434890 < baseStart_1434890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434907 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 1, 1, 3]
def baseStart_1434907 : Nat := 118140960795 + 1434907 * 2 ^ 59
def prefixEnd_1434907 : Nat := 4983230072969 + 3 ^ 40 * 1434907 * 2
def baseEnd_1434907 : Nat := 736796985501122653463489

theorem tailTrace_1434907 : CollatzResearch.WordTrace tailWord_1434907 prefixEnd_1434907 736796985501122653463489 := by
  unfold tailWord_1434907
  simp only [CollatzResearch.WordTrace]
  refine ⟨52335357812584476450278975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34890238541722984300185983 52335357812584476450278975)
  ·
    refine ⟨78503036718876714675418463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52335357812584476450278975 78503036718876714675418463)
    ·
      refine ⟨117754555078315072013127695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78503036718876714675418463 117754555078315072013127695)
      ·
        refine ⟨176631832617472608019691543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117754555078315072013127695 176631832617472608019691543)
        ·
          refine ⟨264947748926208912029537315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176631832617472608019691543 264947748926208912029537315)
          ·
            refine ⟨397421623389313368044305973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264947748926208912029537315 397421623389313368044305973)
            ·
              refine ⟨37258277192748128254153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 397421623389313368044305973 37258277192748128254153685)
              ·
                refine ⟨873240871705034255956727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37258277192748128254153685 873240871705034255956727)
                ·
                  refine ⟨1309861307557551383935091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873240871705034255956727 1309861307557551383935091)
                  ·
                    refine ⟨1964791961336327075902637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309861307557551383935091 1964791961336327075902637)
                    ·
                      refine ⟨736796985501122653463489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964791961336327075902637 736796985501122653463489)
                      ·
                        rfl

theorem cell23_1434907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 1, 3].length) (baseStart_1434907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434907 prefixEnd_1434907 := by exact prefixLift 1434907
  have htrace : WordTrace (prefixWord ++ tailWord_1434907) baseStart_1434907 baseEnd_1434907 := by
    simpa [prefixWord, tailWord_1434907, baseEnd_1434907] using wordTrace_append hprefix tailTrace_1434907
  have hstable : (prefixWord ++ tailWord_1434907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434907).length < 2 ^ (prefixWord ++ tailWord_1434907).sum := by decide
  have hdescent : baseEnd_1434907 < baseStart_1434907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434917 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_1434917 : Nat := 118140960795 + 1434917 * 2 ^ 59
def prefixEnd_1434917 : Nat := 4983230072969 + 3 ^ 40 * 1434917 * 2
def baseEnd_1434917 : Nat := 736802120307667614338443

theorem tailTrace_1434917 : CollatzResearch.WordTrace tailWord_1434917 prefixEnd_1434917 736802120307667614338443 := by
  unfold tailWord_1434917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52335722542548248158143005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34890481695032165438762003 52335722542548248158143005)
  ·
    refine ⟨19625895953455593059303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52335722542548248158143005 19625895953455593059303627)
    ·
      refine ⟨29438843930183389588955441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19625895953455593059303627 29438843930183389588955441)
      ·
        refine ⟨22079132947637542191716581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29438843930183389588955441 22079132947637542191716581)
        ·
          refine ⟨4139837427682039160946859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22079132947637542191716581 4139837427682039160946859)
          ·
            refine ⟨6209756141523058741420289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139837427682039160946859 6209756141523058741420289)
            ·
              refine ⟨4657317106142294056065217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209756141523058741420289 4657317106142294056065217)
              ·
                refine ⟨3492987829606720542048913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657317106142294056065217 3492987829606720542048913)
                ·
                  refine ⟨2619740872205040406536685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492987829606720542048913 2619740872205040406536685)
                  ·
                    refine ⟨982402827076890152451257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619740872205040406536685 982402827076890152451257)
                    ·
                      refine ⟨736802120307667614338443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982402827076890152451257 736802120307667614338443)
                      ·
                        rfl

theorem cell23_1434917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_1434917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434917 prefixEnd_1434917 := by exact prefixLift 1434917
  have htrace : WordTrace (prefixWord ++ tailWord_1434917) baseStart_1434917 baseEnd_1434917 := by
    simpa [prefixWord, tailWord_1434917, baseEnd_1434917] using wordTrace_append hprefix tailTrace_1434917
  have hstable : (prefixWord ++ tailWord_1434917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434917).length < 2 ^ (prefixWord ++ tailWord_1434917).sum := by decide
  have hdescent : baseEnd_1434917 < baseStart_1434917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434930 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1434930 : Nat := 118140960795 + 1434930 * 2 ^ 59
def prefixEnd_1434930 : Nat := 4983230072969 + 3 ^ 40 * 1434930 * 2
def baseEnd_1434930 : Nat := 736808795556176063475883

theorem tailTrace_1434930 : CollatzResearch.WordTrace tailWord_1434930 prefixEnd_1434930 736808795556176063475883 := by
  unfold tailWord_1434930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084049172875287844591561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34890797794334100918910829 13084049172875287844591561)
  ·
    refine ⟨9813036879656465883443671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13084049172875287844591561 9813036879656465883443671)
    ·
      refine ⟨14719555319484698825165507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9813036879656465883443671 14719555319484698825165507)
      ·
        refine ⟨22079332979227048237748261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14719555319484698825165507 22079332979227048237748261)
        ·
          refine ⟨4139874933605071544577799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22079332979227048237748261 4139874933605071544577799)
          ·
            refine ⟨6209812400407607316866699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139874933605071544577799 6209812400407607316866699)
            ·
              refine ⟨9314718600611410975300049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209812400407607316866699 9314718600611410975300049)
              ·
                refine ⟨6986038950458558231475037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9314718600611410975300049 6986038950458558231475037)
                ·
                  refine ⟨2619764606421959336803139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6986038950458558231475037 2619764606421959336803139)
                  ·
                    refine ⟨3929646909632939005204709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619764606421959336803139 3929646909632939005204709)
                    ·
                      refine ⟨736808795556176063475883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3929646909632939005204709 736808795556176063475883)
                      ·
                        rfl

theorem cell23_1434930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1434930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434930 prefixEnd_1434930 := by exact prefixLift 1434930
  have htrace : WordTrace (prefixWord ++ tailWord_1434930) baseStart_1434930 baseEnd_1434930 := by
    simpa [prefixWord, tailWord_1434930, baseEnd_1434930] using wordTrace_append hprefix tailTrace_1434930
  have hstable : (prefixWord ++ tailWord_1434930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434930).length < 2 ^ (prefixWord ++ tailWord_1434930).sum := by decide
  have hdescent : baseEnd_1434930 < baseStart_1434930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434940 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1434940 : Nat := 118140960795 + 1434940 * 2 ^ 59
def prefixEnd_1434940 : Nat := 4983230072969 + 3 ^ 40 * 1434940 * 2
def baseEnd_1434940 : Nat := 245604643454240341450279

theorem tailTrace_1434940 : CollatzResearch.WordTrace tailWord_1434940 prefixEnd_1434940 245604643454240341450279 := by
  unfold tailWord_1434940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168280710732461543115137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34891040947643282057486849 26168280710732461543115137)
  ·
    refine ⟨19626210533049346157336353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26168280710732461543115137 19626210533049346157336353)
    ·
      refine ⟨14719657899787009618002265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19626210533049346157336353 14719657899787009618002265)
      ·
        refine ⟨11039743424840257213501699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14719657899787009618002265 11039743424840257213501699)
        ·
          refine ⟨16559615137260385820252549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039743424840257213501699 16559615137260385820252549)
          ·
            refine ⟨3104927838236322341297353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16559615137260385820252549 3104927838236322341297353)
            ·
              refine ⟨2328695878677241755973015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104927838236322341297353 2328695878677241755973015)
              ·
                refine ⟨3493043818015862633959523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328695878677241755973015 3493043818015862633959523)
                ·
                  refine ⟨5239565727023793950939285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493043818015862633959523 5239565727023793950939285)
                  ·
                    refine ⟨245604643454240341450279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5239565727023793950939285 245604643454240341450279)
                    ·
                      rfl

theorem cell23_1434940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1434940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434940 prefixEnd_1434940 := by exact prefixLift 1434940
  have htrace : WordTrace (prefixWord ++ tailWord_1434940) baseStart_1434940 baseEnd_1434940 := by
    simpa [prefixWord, tailWord_1434940, baseEnd_1434940] using wordTrace_append hprefix tailTrace_1434940
  have hstable : (prefixWord ++ tailWord_1434940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434940).length < 2 ^ (prefixWord ++ tailWord_1434940).sum := by decide
  have hdescent : baseEnd_1434940 < baseStart_1434940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434967 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1434967 : Nat := 118140960795 + 1434967 * 2 ^ 59
def prefixEnd_1434967 : Nat := 4983230072969 + 3 ^ 40 * 1434967 * 2
def baseEnd_1434967 : Nat := 736827794340392418713213

theorem tailTrace_1434967 : CollatzResearch.WordTrace tailWord_1434967 prefixEnd_1434967 736827794340392418713213 := by
  unfold tailWord_1434967
  simp only [CollatzResearch.WordTrace]
  refine ⟨52337546192367106697463155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34891697461578071131642103 52337546192367106697463155)
  ·
    refine ⟨78506319288550660046194733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52337546192367106697463155 78506319288550660046194733)
    ·
      refine ⟨29439869733206497517323025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78506319288550660046194733 29439869733206497517323025)
      ·
        refine ⟨22079902299904873137992269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29439869733206497517323025 22079902299904873137992269)
        ·
          refine ⟨8279963362464327426747101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22079902299904873137992269 8279963362464327426747101)
          ·
            refine ⟨3104986260924122785030163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8279963362464327426747101 3104986260924122785030163)
            ·
              refine ⟨4657479391386184177545245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104986260924122785030163 4657479391386184177545245)
              ·
                refine ⟨1746554771769819066579467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4657479391386184177545245 1746554771769819066579467)
                ·
                  refine ⟨2619832157654728599869201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746554771769819066579467 2619832157654728599869201)
                  ·
                    refine ⟨1964874118241046449901901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2619832157654728599869201 1964874118241046449901901)
                    ·
                      refine ⟨736827794340392418713213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964874118241046449901901 736827794340392418713213)
                      ·
                        rfl

theorem cell23_1434967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1434967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1434967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1434967 prefixEnd_1434967 := by exact prefixLift 1434967
  have htrace : WordTrace (prefixWord ++ tailWord_1434967) baseStart_1434967 baseEnd_1434967 := by
    simpa [prefixWord, tailWord_1434967, baseEnd_1434967] using wordTrace_append hprefix tailTrace_1434967
  have hstable : (prefixWord ++ tailWord_1434967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434967).length < 2 ^ (prefixWord ++ tailWord_1434967).sum := by decide
  have hdescent : baseEnd_1434967 < baseStart_1434967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435013 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1435013 : Nat := 118140960795 + 1435013 * 2 ^ 59
def prefixEnd_1435013 : Nat := 4983230072969 + 3 ^ 40 * 1435013 * 2
def baseEnd_1435013 : Nat := 245617138150166412912667

theorem tailTrace_1435013 : CollatzResearch.WordTrace tailWord_1435013 prefixEnd_1435013 245617138150166412912667 := by
  unfold tailWord_1435013
  simp only [CollatzResearch.WordTrace]
  refine ⟨52339223950200456553637693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34892815966800304369091795 52339223950200456553637693)
  ·
    refine ⟨19627208981325171207614135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52339223950200456553637693 19627208981325171207614135)
    ·
      refine ⟨29440813471987756811421203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19627208981325171207614135 29440813471987756811421203)
      ·
        refine ⟨44161220207981635217131805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29440813471987756811421203 44161220207981635217131805)
        ·
          refine ⟨16560457577993113206424427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44161220207981635217131805 16560457577993113206424427)
          ·
            refine ⟨24840686366989669809636641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16560457577993113206424427 24840686366989669809636641)
            ·
              refine ⟨18630514775242252357227481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24840686366989669809636641 18630514775242252357227481)
              ·
                refine ⟨13972886081431689267920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18630514775242252357227481 13972886081431689267920611)
                ·
                  refine ⟨20959329122147533901880917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972886081431689267920611 20959329122147533901880917)
                  ·
                    refine ⟨245617138150166412912667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20959329122147533901880917 245617138150166412912667)
                    ·
                      rfl

theorem cell23_1435013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1435013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435013 prefixEnd_1435013 := by exact prefixLift 1435013
  have htrace : WordTrace (prefixWord ++ tailWord_1435013) baseStart_1435013 baseEnd_1435013 := by
    simpa [prefixWord, tailWord_1435013, baseEnd_1435013] using wordTrace_append hprefix tailTrace_1435013
  have hstable : (prefixWord ++ tailWord_1435013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435013).length < 2 ^ (prefixWord ++ tailWord_1435013).sum := by decide
  have hdescent : baseEnd_1435013 < baseStart_1435013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435040 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1435040 : Nat := 118140960795 + 1435040 * 2 ^ 59
def prefixEnd_1435040 : Nat := 4983230072969 + 3 ^ 40 * 1435040 * 2
def baseEnd_1435040 : Nat := 736865278428170633100377

theorem tailTrace_1435040 : CollatzResearch.WordTrace tailWord_1435040 prefixEnd_1435040 736865278428170633100377 := by
  unfold tailWord_1435040
  simp only [CollatzResearch.WordTrace]
  refine ⟨26170104360551320082435287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34893472480735093443247049 26170104360551320082435287)
  ·
    refine ⟨39255156540826980123652931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26170104360551320082435287 39255156540826980123652931)
    ·
      refine ⟨58882734811240470185479397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39255156540826980123652931 58882734811240470185479397)
      ·
        refine ⟨11040512777107588159777387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58882734811240470185479397 11040512777107588159777387)
        ·
          refine ⟨16560769165661382239666081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040512777107588159777387 16560769165661382239666081)
          ·
            refine ⟨12420576874246036679749561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16560769165661382239666081 12420576874246036679749561)
            ·
              refine ⟨9315432655684527509812171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12420576874246036679749561 9315432655684527509812171)
              ·
                refine ⟨13973148983526791264718257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315432655684527509812171 13973148983526791264718257)
                ·
                  refine ⟨10479861737645093448538693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13973148983526791264718257 10479861737645093448538693)
                  ·
                    refine ⟨1964974075808455021601005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10479861737645093448538693 1964974075808455021601005)
                    ·
                      refine ⟨736865278428170633100377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1964974075808455021601005 736865278428170633100377)
                      ·
                        rfl

theorem cell23_1435040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1435040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435040 prefixEnd_1435040 := by exact prefixLift 1435040
  have htrace : WordTrace (prefixWord ++ tailWord_1435040) baseStart_1435040 baseEnd_1435040 := by
    simpa [prefixWord, tailWord_1435040, baseEnd_1435040] using wordTrace_append hprefix tailTrace_1435040
  have hstable : (prefixWord ++ tailWord_1435040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435040).length < 2 ^ (prefixWord ++ tailWord_1435040).sum := by decide
  have hdescent : baseEnd_1435040 < baseStart_1435040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435097 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 5, 2]
def baseStart_1435097 : Nat := 118140960795 + 1435097 * 2 ^ 59
def prefixEnd_1435097 : Nat := 4983230072969 + 3 ^ 40 * 1435097 * 2
def baseEnd_1435097 : Nat := 736894546825476910087615

theorem tailTrace_1435097 : CollatzResearch.WordTrace tailWord_1435097 prefixEnd_1435097 736894546825476910087615 := by
  unfold tailWord_1435097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52342287681896138899695545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34894858454597425933130363 52342287681896138899695545)
  ·
    refine ⟨39256715761422104174771659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52342287681896138899695545 39256715761422104174771659)
    ·
      refine ⟨58885073642133156262157489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39256715761422104174771659 58885073642133156262157489)
      ·
        refine ⟨44163805231599867196618117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58885073642133156262157489 44163805231599867196618117)
        ·
          refine ⟨8280713480924975099365897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44163805231599867196618117 8280713480924975099365897)
          ·
            refine ⟨6210535110693731324524423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8280713480924975099365897 6210535110693731324524423)
            ·
              refine ⟨9315802666040596986786635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210535110693731324524423 9315802666040596986786635)
              ·
                refine ⟨13973703999060895480179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315802666040596986786635 13973703999060895480179953)
                ·
                  refine ⟨10480277999295671610134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13973703999060895480179953 10480277999295671610134965)
                  ·
                    refine ⟨982526062433969213450153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10480277999295671610134965 982526062433969213450153)
                    ·
                      refine ⟨736894546825476910087615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982526062433969213450153 736894546825476910087615)
                      ·
                        rfl

theorem cell23_1435097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_1435097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435097 prefixEnd_1435097 := by exact prefixLift 1435097
  have htrace : WordTrace (prefixWord ++ tailWord_1435097) baseStart_1435097 baseEnd_1435097 := by
    simpa [prefixWord, tailWord_1435097, baseEnd_1435097] using wordTrace_append hprefix tailTrace_1435097
  have hstable : (prefixWord ++ tailWord_1435097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435097).length < 2 ^ (prefixWord ++ tailWord_1435097).sum := by decide
  have hdescent : baseEnd_1435097 < baseStart_1435097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435217 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_1435217 : Nat := 118140960795 + 1435217 * 2 ^ 59
def prefixEnd_1435217 : Nat := 4983230072969 + 3 ^ 40 * 1435217 * 2
def baseEnd_1435217 : Nat := 736956164504016440587063

theorem tailTrace_1435217 : CollatzResearch.WordTrace tailWord_1435217 prefixEnd_1435217 736956164504016440587063 := by
  unfold tailWord_1435217
  simp only [CollatzResearch.WordTrace]
  refine ⟨52346664441461399394063905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34897776294307599596042603 52346664441461399394063905)
  ·
    refine ⟨39259998331096049545547929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52346664441461399394063905 39259998331096049545547929)
    ·
      refine ⟨29444998748322037159160947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39259998331096049545547929 29444998748322037159160947)
      ·
        refine ⟨44167498122483055738741421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29444998748322037159160947 44167498122483055738741421)
        ·
          refine ⟨16562811795931145902028033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44167498122483055738741421 16562811795931145902028033)
          ·
            refine ⟨12422108846948359426521025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16562811795931145902028033 12422108846948359426521025)
            ·
              refine ⟨9316581635211269569890769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12422108846948359426521025 9316581635211269569890769)
              ·
                refine ⟨6987436226408452177418077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9316581635211269569890769 6987436226408452177418077)
                ·
                  refine ⟨2620288584903169566531779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6987436226408452177418077 2620288584903169566531779)
                  ·
                    refine ⟨3930432877354754349797669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2620288584903169566531779 3930432877354754349797669)
                    ·
                      refine ⟨736956164504016440587063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3930432877354754349797669 736956164504016440587063)
                      ·
                        rfl

theorem cell23_1435217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_1435217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435217 prefixEnd_1435217 := by exact prefixLift 1435217
  have htrace : WordTrace (prefixWord ++ tailWord_1435217) baseStart_1435217 baseEnd_1435217 := by
    simpa [prefixWord, tailWord_1435217, baseEnd_1435217] using wordTrace_append hprefix tailTrace_1435217
  have hstable : (prefixWord ++ tailWord_1435217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435217).length < 2 ^ (prefixWord ++ tailWord_1435217).sum := by decide
  have hdescent : baseEnd_1435217 < baseStart_1435217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435261 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1435261 : Nat := 118140960795 + 1435261 * 2 ^ 59
def prefixEnd_1435261 : Nat := 4983230072969 + 3 ^ 40 * 1435261 * 2
def baseEnd_1435261 : Nat := 245659585884271422812287

theorem tailTrace_1435261 : CollatzResearch.WordTrace tailWord_1435261 prefixEnd_1435261 245659585884271422812287 := by
  unfold tailWord_1435261
  simp only [CollatzResearch.WordTrace]
  refine ⟨52348269253301994908665637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34898846168867996605777091 52348269253301994908665637)
  ·
    refine ⟨9815300484994124045374807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52348269253301994908665637 9815300484994124045374807)
    ·
      refine ⟨14722950727491186068062211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815300484994124045374807 14722950727491186068062211)
      ·
        refine ⟨22084426091236779102093317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722950727491186068062211 22084426091236779102093317)
        ·
          refine ⟨4140829892106896081642497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22084426091236779102093317 4140829892106896081642497)
          ·
            refine ⟨3105622419080172061231873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4140829892106896081642497 3105622419080172061231873)
            ·
              refine ⟨2329216814310129045923905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105622419080172061231873 2329216814310129045923905)
              ·
                refine ⟨1746912610732596784442929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329216814310129045923905 1746912610732596784442929)
                ·
                  refine ⟨1310184458049447588332197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746912610732596784442929 1310184458049447588332197)
                  ·
                    refine ⟨245659585884271422812287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310184458049447588332197 245659585884271422812287)
                    ·
                      rfl

theorem cell23_1435261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1435261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435261 prefixEnd_1435261 := by exact prefixLift 1435261
  have htrace : WordTrace (prefixWord ++ tailWord_1435261) baseStart_1435261 baseEnd_1435261 := by
    simpa [prefixWord, tailWord_1435261, baseEnd_1435261] using wordTrace_append hprefix tailTrace_1435261
  have hstable : (prefixWord ++ tailWord_1435261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435261).length < 2 ^ (prefixWord ++ tailWord_1435261).sum := by decide
  have hdescent : baseEnd_1435261 < baseStart_1435261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435267 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3]
def baseStart_1435267 : Nat := 118140960795 + 1435267 * 2 ^ 59
def prefixEnd_1435267 : Nat := 4983230072969 + 3 ^ 40 * 1435267 * 2
def baseEnd_1435267 : Nat := 736981838536741244961833

theorem tailTrace_1435267 : CollatzResearch.WordTrace tailWord_1435267 prefixEnd_1435267 736981838536741244961833 := by
  unfold tailWord_1435267
  simp only [CollatzResearch.WordTrace]
  refine ⟨52348488091280257933384055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34898992060853505288922703 52348488091280257933384055)
  ·
    refine ⟨78522732136920386900076083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52348488091280257933384055 78522732136920386900076083)
    ·
      refine ⟨117784098205380580350114125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78522732136920386900076083 117784098205380580350114125)
      ·
        refine ⟨44169036827017717631292797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117784098205380580350114125 44169036827017717631292797)
        ·
          refine ⟨16563388810131644111734799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44169036827017717631292797 16563388810131644111734799)
          ·
            refine ⟨24845083215197466167602199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16563388810131644111734799 24845083215197466167602199)
            ·
              refine ⟨37267624822796199251403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24845083215197466167602199 37267624822796199251403299)
              ·
                refine ⟨55901437234194298877104949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37267624822796199251403299 55901437234194298877104949)
                ·
                  refine ⟨5240759740705715519728589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55901437234194298877104949 5240759740705715519728589)
                  ·
                    refine ⟨1965284902764643319898221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5240759740705715519728589 1965284902764643319898221)
                    ·
                      refine ⟨736981838536741244961833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965284902764643319898221 736981838536741244961833)
                      ·
                        rfl

theorem cell23_1435267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_1435267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435267 prefixEnd_1435267 := by exact prefixLift 1435267
  have htrace : WordTrace (prefixWord ++ tailWord_1435267) baseStart_1435267 baseEnd_1435267 := by
    simpa [prefixWord, tailWord_1435267, baseEnd_1435267] using wordTrace_append hprefix tailTrace_1435267
  have hstable : (prefixWord ++ tailWord_1435267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435267).length < 2 ^ (prefixWord ++ tailWord_1435267).sum := by decide
  have hdescent : baseEnd_1435267 < baseStart_1435267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435274 : List Nat := [3, 1, 2, 3, 2, 3, 1, 8]
def baseStart_1435274 : Nat := 118140960795 + 1435274 * 2 ^ 59
def prefixEnd_1435274 : Nat := 4983230072969 + 3 ^ 40 * 1435274 * 2
def baseEnd_1435274 : Nat := 27295756774123063613863

theorem tailTrace_1435274 : CollatzResearch.WordTrace tailWord_1435274 prefixEnd_1435274 27295756774123063613863 := by
  unfold tailWord_1435274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087185850563724532222219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34899162268169932085925917 13087185850563724532222219)
  ·
    refine ⟨19630778775845586798333329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13087185850563724532222219 19630778775845586798333329)
    ·
      refine ⟨14723084081884190098749997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19630778775845586798333329 14723084081884190098749997)
      ·
        refine ⟨5521156530706571287031249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14723084081884190098749997 5521156530706571287031249)
        ·
          refine ⟨4140867398029928465273437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5521156530706571287031249 4140867398029928465273437)
          ·
            refine ⟨1552825274261223174477539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4140867398029928465273437 1552825274261223174477539)
            ·
              refine ⟨2329237911391834761716309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552825274261223174477539 2329237911391834761716309)
              ·
                refine ⟨27295756774123063613863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2329237911391834761716309 27295756774123063613863)
                ·
                  rfl

theorem cell23_1435274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_1435274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435274 prefixEnd_1435274 := by exact prefixLift 1435274
  have htrace : WordTrace (prefixWord ++ tailWord_1435274) baseStart_1435274 baseEnd_1435274 := by
    simpa [prefixWord, tailWord_1435274, baseEnd_1435274] using wordTrace_append hprefix tailTrace_1435274
  have hstable : (prefixWord ++ tailWord_1435274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435274).length < 2 ^ (prefixWord ++ tailWord_1435274).sum := by decide
  have hdescent : baseEnd_1435274 < baseStart_1435274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435311 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 1, 3, 2]
def baseStart_1435311 : Nat := 118140960795 + 1435311 * 2 ^ 59
def prefixEnd_1435311 : Nat := 4983230072969 + 3 ^ 40 * 1435311 * 2
def baseEnd_1435311 : Nat := 737004431685539072811631

theorem tailTrace_1435311 : CollatzResearch.WordTrace tailWord_1435311 prefixEnd_1435311 737004431685539072811631 := by
  unfold tailWord_1435311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350092903120853447985787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34900061935413902298657191 52350092903120853447985787)
  ·
    refine ⟨78525139354681280171978681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52350092903120853447985787 78525139354681280171978681)
    ·
      refine ⟨58893854516010960128984011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78525139354681280171978681 58893854516010960128984011)
      ·
        refine ⟨88340781774016440193476017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58893854516010960128984011 88340781774016440193476017)
        ·
          refine ⟨66255586330512330145107013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88340781774016440193476017 66255586330512330145107013)
          ·
            refine ⟨12422922436971061902207565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66255586330512330145107013 12422922436971061902207565)
            ·
              refine ⟨4658595913864148213327837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12422922436971061902207565 4658595913864148213327837)
              ·
                refine ⟨1746973467699055579997939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4658595913864148213327837 1746973467699055579997939)
                ·
                  refine ⟨2620460201548583369996909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746973467699055579997939 2620460201548583369996909)
                  ·
                    refine ⟨982672575580718763748841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620460201548583369996909 982672575580718763748841)
                    ·
                      refine ⟨737004431685539072811631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982672575580718763748841 737004431685539072811631)
                      ·
                        rfl

theorem cell23_1435311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3, 2].length) (baseStart_1435311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435311 prefixEnd_1435311 := by exact prefixLift 1435311
  have htrace : WordTrace (prefixWord ++ tailWord_1435311) baseStart_1435311 baseEnd_1435311 := by
    simpa [prefixWord, tailWord_1435311, baseEnd_1435311] using wordTrace_append hprefix tailTrace_1435311
  have hstable : (prefixWord ++ tailWord_1435311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435311).length < 2 ^ (prefixWord ++ tailWord_1435311).sum := by decide
  have hdescent : baseEnd_1435311 < baseStart_1435311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435481 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_1435481 : Nat := 118140960795 + 1435481 * 2 ^ 59
def prefixEnd_1435481 : Nat := 4983230072969 + 3 ^ 40 * 1435481 * 2
def baseEnd_1435481 : Nat := 737091723396803407685849

theorem tailTrace_1435481 : CollatzResearch.WordTrace tailWord_1435481 prefixEnd_1435481 737091723396803407685849 := by
  unfold tailWord_1435481
  simp only [CollatzResearch.WordTrace]
  refine ⟨52356293312504972481674297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34904195541669981654449531 52356293312504972481674297)
  ·
    refine ⟨39267219984378729361255723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52356293312504972481674297 39267219984378729361255723)
    ·
      refine ⟨58900829976568094041883585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39267219984378729361255723 58900829976568094041883585)
      ·
        refine ⟨44175622482426070531412689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58900829976568094041883585 44175622482426070531412689)
        ·
          refine ⟨33131716861819552898559517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44175622482426070531412689 33131716861819552898559517)
          ·
            refine ⟨12424393823182332336959819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33131716861819552898559517 12424393823182332336959819)
            ·
              refine ⟨18636590734773498505439729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424393823182332336959819 18636590734773498505439729)
              ·
                refine ⟨13977443051080123879079797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18636590734773498505439729 13977443051080123879079797)
                ·
                  refine ⟨1310385286038761613663731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13977443051080123879079797 1310385286038761613663731)
                  ·
                    refine ⟨1965577929058142420495597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1310385286038761613663731 1965577929058142420495597)
                    ·
                      refine ⟨737091723396803407685849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965577929058142420495597 737091723396803407685849)
                      ·
                        rfl

theorem cell23_1435481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_1435481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435481 prefixEnd_1435481 := by exact prefixLift 1435481
  have htrace : WordTrace (prefixWord ++ tailWord_1435481) baseStart_1435481 baseEnd_1435481 := by
    simpa [prefixWord, tailWord_1435481, baseEnd_1435481] using wordTrace_append hprefix tailTrace_1435481
  have hstable : (prefixWord ++ tailWord_1435481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435481).length < 2 ^ (prefixWord ++ tailWord_1435481).sum := by decide
  have hdescent : baseEnd_1435481 < baseStart_1435481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435541 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_1435541 : Nat := 118140960795 + 1435541 * 2 ^ 59
def prefixEnd_1435541 : Nat := 4983230072969 + 3 ^ 40 * 1435541 * 2
def baseEnd_1435541 : Nat := 737122532236073172935573

theorem tailTrace_1435541 : CollatzResearch.WordTrace tailWord_1435541 prefixEnd_1435541 737122532236073172935573 := by
  unfold tailWord_1435541
  simp only [CollatzResearch.WordTrace]
  refine ⟨52358481692287602728858477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34905654461525068485905651 52358481692287602728858477)
  ·
    refine ⟨19634430634607851023321929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52358481692287602728858477 19634430634607851023321929)
    ·
      refine ⟨14725822975955888267491447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19634430634607851023321929 14725822975955888267491447)
      ·
        refine ⟨22088734463933832401237171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14725822975955888267491447 22088734463933832401237171)
        ·
          refine ⟨33133101695900748601855757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22088734463933832401237171 33133101695900748601855757)
          ·
            refine ⟨12424913135962780725695909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33133101695900748601855757 12424913135962780725695909)
            ·
              refine ⟨2329671212993021386067983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12424913135962780725695909 2329671212993021386067983)
              ·
                refine ⟨3494506819489532079101975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329671212993021386067983 3494506819489532079101975)
                ·
                  refine ⟨5241760229234298118652963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494506819489532079101975 5241760229234298118652963)
                  ·
                    refine ⟨7862640343851447177979445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241760229234298118652963 7862640343851447177979445)
                    ·
                      refine ⟨737122532236073172935573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7862640343851447177979445 737122532236073172935573)
                      ·
                        rfl

theorem cell23_1435541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_1435541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435541 prefixEnd_1435541 := by exact prefixLift 1435541
  have htrace : WordTrace (prefixWord ++ tailWord_1435541) baseStart_1435541 baseEnd_1435541 := by
    simpa [prefixWord, tailWord_1435541, baseEnd_1435541] using wordTrace_append hprefix tailTrace_1435541
  have hstable : (prefixWord ++ tailWord_1435541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435541).length < 2 ^ (prefixWord ++ tailWord_1435541).sum := by decide
  have hdescent : baseEnd_1435541 < baseStart_1435541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435548 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1435548 : Nat := 118140960795 + 1435548 * 2 ^ 59
def prefixEnd_1435548 : Nat := 4983230072969 + 3 ^ 40 * 1435548 * 2
def baseEnd_1435548 : Nat := 245708708866884881849347

theorem tailTrace_1435548 : CollatzResearch.WordTrace tailWord_1435548 prefixEnd_1435548 245708708866884881849347 := by
  unfold tailWord_1435548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179368501631121462181649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34905824668841495282908865 26179368501631121462181649)
  ·
    refine ⟨19634526376223341096636237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26179368501631121462181649 19634526376223341096636237)
    ·
      refine ⟨7362947391083752911238589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19634526376223341096636237 7362947391083752911238589)
      ·
        refine ⟨2761105271656407341714471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7362947391083752911238589 2761105271656407341714471)
        ·
          refine ⟨4141657907484611012571707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761105271656407341714471 4141657907484611012571707)
          ·
            refine ⟨6212486861226916518857561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141657907484611012571707 6212486861226916518857561)
            ·
              refine ⟨4659365145920187389143171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6212486861226916518857561 4659365145920187389143171)
              ·
                refine ⟨6989047718880281083714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659365145920187389143171 6989047718880281083714757)
                ·
                  refine ⟨1310446447290052703196517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6989047718880281083714757 1310446447290052703196517)
                  ·
                    refine ⟨245708708866884881849347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310446447290052703196517 245708708866884881849347)
                    ·
                      rfl

theorem cell23_1435548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1435548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435548 prefixEnd_1435548 := by exact prefixLift 1435548
  have htrace : WordTrace (prefixWord ++ tailWord_1435548) baseStart_1435548 baseEnd_1435548 := by
    simpa [prefixWord, tailWord_1435548, baseEnd_1435548] using wordTrace_append hprefix tailTrace_1435548
  have hstable : (prefixWord ++ tailWord_1435548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435548).length < 2 ^ (prefixWord ++ tailWord_1435548).sum := by decide
  have hdescent : baseEnd_1435548 < baseStart_1435548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435571 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3]
def baseStart_1435571 : Nat := 118140960795 + 1435571 * 2 ^ 59
def prefixEnd_1435571 : Nat := 4983230072969 + 3 ^ 40 * 1435571 * 2
def baseEnd_1435571 : Nat := 737137936655708055560435

theorem tailTrace_1435571 : CollatzResearch.WordTrace tailWord_1435571 prefixEnd_1435571 737137936655708055560435 := by
  unfold tailWord_1435571
  simp only [CollatzResearch.WordTrace]
  refine ⟨52359575882178917852450567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34906383921452611901633711 52359575882178917852450567)
  ·
    refine ⟨78539363823268376778675851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52359575882178917852450567 78539363823268376778675851)
    ·
      refine ⟨117809045734902565168013777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78539363823268376778675851 117809045734902565168013777)
      ·
        refine ⟨88356784301176923876010333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117809045734902565168013777 88356784301176923876010333)
        ·
          refine ⟨33133794112941346453503875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88356784301176923876010333 33133794112941346453503875)
          ·
            refine ⟨49700691169412019680255813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33133794112941346453503875 49700691169412019680255813)
            ·
              refine ⟨9318879594264753690047965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49700691169412019680255813 9318879594264753690047965)
              ·
                refine ⟨3494579847849282633767987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9318879594264753690047965 3494579847849282633767987)
                ·
                  refine ⟨5241869771773923950651981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494579847849282633767987 5241869771773923950651981)
                  ·
                    refine ⟨1965701164415221481494493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5241869771773923950651981 1965701164415221481494493)
                    ·
                      refine ⟨737137936655708055560435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965701164415221481494493 737137936655708055560435)
                      ·
                        rfl

theorem cell23_1435571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_1435571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435571 prefixEnd_1435571 := by exact prefixLift 1435571
  have htrace : WordTrace (prefixWord ++ tailWord_1435571) baseStart_1435571 baseEnd_1435571 := by
    simpa [prefixWord, tailWord_1435571, baseEnd_1435571] using wordTrace_append hprefix tailTrace_1435571
  have hstable : (prefixWord ++ tailWord_1435571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435571).length < 2 ^ (prefixWord ++ tailWord_1435571).sum := by decide
  have hdescent : baseEnd_1435571 < baseStart_1435571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435605 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1435605 : Nat := 118140960795 + 1435605 * 2 ^ 59
def prefixEnd_1435605 : Nat := 4983230072969 + 3 ^ 40 * 1435605 * 2
def baseEnd_1435605 : Nat := 737155394997960922535279

theorem tailTrace_1435605 : CollatzResearch.WordTrace tailWord_1435605 prefixEnd_1435605 737155394997960922535279 := by
  unfold tailWord_1435605
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360815964055741659188269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34907210642703827772792179 52360815964055741659188269)
  ·
    refine ⟨19635305986520903122195601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52360815964055741659188269 19635305986520903122195601)
    ·
      refine ⟨14726479489890677341646701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19635305986520903122195601 14726479489890677341646701)
      ·
        refine ⟨5522429808709004003117513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14726479489890677341646701 5522429808709004003117513)
        ·
          refine ⟨4141822356531753002338135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522429808709004003117513 4141822356531753002338135)
          ·
            refine ⟨6212733534797629503507203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141822356531753002338135 6212733534797629503507203)
            ·
              refine ⟨9319100302196444255260805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212733534797629503507203 9319100302196444255260805)
              ·
                refine ⟨1747331306661833297861401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9319100302196444255260805 1747331306661833297861401)
                ·
                  refine ⟨1310498479996374973396051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747331306661833297861401 1310498479996374973396051)
                  ·
                    refine ⟨1965747719994562460094077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1310498479996374973396051 1965747719994562460094077)
                    ·
                      refine ⟨737155394997960922535279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965747719994562460094077 737155394997960922535279)
                      ·
                        rfl

theorem cell23_1435605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1435605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435605 prefixEnd_1435605 := by exact prefixLift 1435605
  have htrace : WordTrace (prefixWord ++ tailWord_1435605) baseStart_1435605 baseEnd_1435605 := by
    simpa [prefixWord, tailWord_1435605, baseEnd_1435605] using wordTrace_append hprefix tailTrace_1435605
  have hstable : (prefixWord ++ tailWord_1435605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435605).length < 2 ^ (prefixWord ++ tailWord_1435605).sum := by decide
  have hdescent : baseEnd_1435605 < baseStart_1435605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435606 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1435606 : Nat := 118140960795 + 1435606 * 2 ^ 59
def prefixEnd_1435606 : Nat := 4983230072969 + 3 ^ 40 * 1435606 * 2
def baseEnd_1435606 : Nat := 737155908478615418622775

theorem tailTrace_1435606 : CollatzResearch.WordTrace tailWord_1435606 prefixEnd_1435606 737155908478615418622775 := by
  unfold tailWord_1435606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272553277315757426873417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34907234958034745886649781 3272553277315757426873417)
  ·
    refine ⟨2454414957986818070155063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3272553277315757426873417 2454414957986818070155063)
    ·
      refine ⟨3681622436980227105232595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454414957986818070155063 3681622436980227105232595)
      ·
        refine ⟨5522433655470340657848893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681622436980227105232595 5522433655470340657848893)
        ·
          refine ⟨2070912620801377746693335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5522433655470340657848893 2070912620801377746693335)
          ·
            refine ⟨3106368931202066620040003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070912620801377746693335 3106368931202066620040003)
            ·
              refine ⟨4659553396803099930060005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106368931202066620040003 4659553396803099930060005)
              ·
                refine ⟨873666261900581236886251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4659553396803099930060005 873666261900581236886251)
                ·
                  refine ⟨1310499392850871855329377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873666261900581236886251 1310499392850871855329377)
                  ·
                    refine ⟨982874544638153891497033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1310499392850871855329377 982874544638153891497033)
                    ·
                      refine ⟨737155908478615418622775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 982874544638153891497033 737155908478615418622775)
                      ·
                        rfl

theorem cell23_1435606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1435606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435606 prefixEnd_1435606 := by exact prefixLift 1435606
  have htrace : WordTrace (prefixWord ++ tailWord_1435606) baseStart_1435606 baseEnd_1435606 := by
    simpa [prefixWord, tailWord_1435606, baseEnd_1435606] using wordTrace_append hprefix tailTrace_1435606
  have hstable : (prefixWord ++ tailWord_1435606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435606).length < 2 ^ (prefixWord ++ tailWord_1435606).sum := by decide
  have hdescent : baseEnd_1435606 < baseStart_1435606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435612 : List Nat := [2, 2, 6, 1, 1, 2, 1, 8]
def baseStart_1435612 : Nat := 118140960795 + 1435612 * 2 ^ 59
def prefixEnd_1435612 : Nat := 4983230072969 + 3 ^ 40 * 1435612 * 2
def baseEnd_1435612 : Nat := 27302184791205273894361

theorem tailTrace_1435612 : CollatzResearch.WordTrace tailWord_1435612 prefixEnd_1435612 27302184791205273894361 := by
  unfold tailWord_1435612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26180535637515190927346545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34907380850020254569795393 26180535637515190927346545)
  ·
    refine ⟨19635401728136393195509909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26180535637515190927346545 19635401728136393195509909)
    ·
      refine ⟨920409456006393431039527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19635401728136393195509909 920409456006393431039527)
      ·
        refine ⟨1380614184009590146559291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920409456006393431039527 1380614184009590146559291)
        ·
          refine ⟨2070921276014385219838937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380614184009590146559291 2070921276014385219838937)
          ·
            refine ⟨1553190957010788914879203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070921276014385219838937 1553190957010788914879203)
            ·
              refine ⟨2329786435516183372318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553190957010788914879203 2329786435516183372318805)
              ·
                refine ⟨27302184791205273894361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2329786435516183372318805 27302184791205273894361)
                ·
                  rfl

theorem cell23_1435612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 8].length) (baseStart_1435612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435612 prefixEnd_1435612 := by exact prefixLift 1435612
  have htrace : WordTrace (prefixWord ++ tailWord_1435612) baseStart_1435612 baseEnd_1435612 := by
    simpa [prefixWord, tailWord_1435612, baseEnd_1435612] using wordTrace_append hprefix tailTrace_1435612
  have hstable : (prefixWord ++ tailWord_1435612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435612).length < 2 ^ (prefixWord ++ tailWord_1435612).sum := by decide
  have hdescent : baseEnd_1435612 < baseStart_1435612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435631 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_1435631 : Nat := 118140960795 + 1435631 * 2 ^ 59
def prefixEnd_1435631 : Nat := 4983230072969 + 3 ^ 40 * 1435631 * 2
def baseEnd_1435631 : Nat := 737168745494977820810159

theorem tailTrace_1435631 : CollatzResearch.WordTrace tailWord_1435631 prefixEnd_1435631 737168745494977820810159 := by
  unfold tailWord_1435631
  simp only [CollatzResearch.WordTrace]
  refine ⟨52361764261961548099634747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34907842841307698733089831 52361764261961548099634747)
  ·
    refine ⟨78542646392942322149452121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52361764261961548099634747 78542646392942322149452121)
    ·
      refine ⟨58906984794706741612089091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78542646392942322149452121 58906984794706741612089091)
      ·
        refine ⟨88360477192060112418133637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58906984794706741612089091 88360477192060112418133637)
        ·
          refine ⟨16567589473511271078400057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88360477192060112418133637 16567589473511271078400057)
          ·
            refine ⟨12425692105133453308800043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16567589473511271078400057 12425692105133453308800043)
            ·
              refine ⟨18638538157700179963200065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425692105133453308800043 18638538157700179963200065)
              ·
                refine ⟨13978903618275134972400049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18638538157700179963200065 13978903618275134972400049)
                ·
                  refine ⟨10484177713706351229300037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13978903618275134972400049 10484177713706351229300037)
                  ·
                    refine ⟨1965783321319940855493757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10484177713706351229300037 1965783321319940855493757)
                    ·
                      refine ⟨737168745494977820810159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965783321319940855493757 737168745494977820810159)
                      ·
                        rfl

theorem cell23_1435631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_1435631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435631 prefixEnd_1435631 := by exact prefixLift 1435631
  have htrace : WordTrace (prefixWord ++ tailWord_1435631) baseStart_1435631 baseEnd_1435631 := by
    simpa [prefixWord, tailWord_1435631, baseEnd_1435631] using wordTrace_append hprefix tailTrace_1435631
  have hstable : (prefixWord ++ tailWord_1435631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435631).length < 2 ^ (prefixWord ++ tailWord_1435631).sum := by decide
  have hdescent : baseEnd_1435631 < baseStart_1435631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435738 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1435738 : Nat := 118140960795 + 1435738 * 2 ^ 59
def prefixEnd_1435738 : Nat := 4983230072969 + 3 ^ 40 * 1435738 * 2
def baseEnd_1435738 : Nat := 737223687925008902172167

theorem tailTrace_1435738 : CollatzResearch.WordTrace tailWord_1435738 prefixEnd_1435738 737223687925008902172167 := by
  unfold tailWord_1435738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091416718143476343444967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34910444581715936915853245 13091416718143476343444967)
  ·
    refine ⟨19637125077215214515167451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13091416718143476343444967 19637125077215214515167451)
    ·
      refine ⟨29455687615822821772751177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19637125077215214515167451 29455687615822821772751177)
      ·
        refine ⟨22091765711867116329563383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29455687615822821772751177 22091765711867116329563383)
        ·
          refine ⟨33137648567800674494345075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22091765711867116329563383 33137648567800674494345075)
          ·
            refine ⟨49706472851701011741517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33137648567800674494345075 49706472851701011741517613)
            ·
              refine ⟨18639927319387879403069105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49706472851701011741517613 18639927319387879403069105)
              ·
                refine ⟨13979945489540909552301829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18639927319387879403069105 13979945489540909552301829)
                ·
                  refine ⟨2621239779288920541056593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13979945489540909552301829 2621239779288920541056593)
                  ·
                    refine ⟨1965929834466690405792445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621239779288920541056593 1965929834466690405792445)
                    ·
                      refine ⟨737223687925008902172167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965929834466690405792445 737223687925008902172167)
                      ·
                        rfl

theorem cell23_1435738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1435738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435738 prefixEnd_1435738 := by exact prefixLift 1435738
  have htrace : WordTrace (prefixWord ++ tailWord_1435738) baseStart_1435738 baseEnd_1435738 := by
    simpa [prefixWord, tailWord_1435738, baseEnd_1435738] using wordTrace_append hprefix tailTrace_1435738
  have hstable : (prefixWord ++ tailWord_1435738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435738).length < 2 ^ (prefixWord ++ tailWord_1435738).sum := by decide
  have hdescent : baseEnd_1435738 < baseStart_1435738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435779 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 1, 4]
def baseStart_1435779 : Nat := 118140960795 + 1435779 * 2 ^ 59
def prefixEnd_1435779 : Nat := 4983230072969 + 3 ^ 40 * 1435779 * 2
def baseEnd_1435779 : Nat := 245748246877281080586493

theorem tailTrace_1435779 : CollatzResearch.WordTrace tailWord_1435779 prefixEnd_1435779 245748246877281080586493 := by
  unfold tailWord_1435779
  simp only [CollatzResearch.WordTrace]
  refine ⟨52367162265425369376022391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34911441510283579584014927 52367162265425369376022391)
  ·
    refine ⟨78550743398138054064033587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52367162265425369376022391 78550743398138054064033587)
    ·
      refine ⟨117826115097207081096050381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78550743398138054064033587 117826115097207081096050381)
      ·
        refine ⟨44184793161452655411018893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117826115097207081096050381 44184793161452655411018893)
        ·
          refine ⟨16569297435544745779132085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44184793161452655411018893 16569297435544745779132085)
          ·
            refine ⟨1553371634582319916793633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16569297435544745779132085 1553371634582319916793633)
            ·
              refine ⟨1165028725936739937595225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553371634582319916793633 1165028725936739937595225)
              ·
                refine ⟨873771544452554953196419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165028725936739937595225 873771544452554953196419)
                ·
                  refine ⟨1310657316678832429794629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873771544452554953196419 1310657316678832429794629)
                  ·
                    refine ⟨245748246877281080586493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310657316678832429794629 245748246877281080586493)
                    ·
                      rfl

theorem cell23_1435779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 4].length) (baseStart_1435779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435779 prefixEnd_1435779 := by exact prefixLift 1435779
  have htrace : WordTrace (prefixWord ++ tailWord_1435779) baseStart_1435779 baseEnd_1435779 := by
    simpa [prefixWord, tailWord_1435779, baseEnd_1435779] using wordTrace_append hprefix tailTrace_1435779
  have hstable : (prefixWord ++ tailWord_1435779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435779).length < 2 ^ (prefixWord ++ tailWord_1435779).sum := by decide
  have hdescent : baseEnd_1435779 < baseStart_1435779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435785 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_1435785 : Nat := 118140960795 + 1435785 * 2 ^ 59
def prefixEnd_1435785 : Nat := 4983230072969 + 3 ^ 40 * 1435785 * 2
def baseEnd_1435785 : Nat := 737247821515770218284451

theorem tailTrace_1435785 : CollatzResearch.WordTrace tailWord_1435785 prefixEnd_1435785 737247821515770218284451 := by
  unfold tailWord_1435785
  simp only [CollatzResearch.WordTrace]
  refine ⟨52367381103403632400740809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34911587402269088267160539 52367381103403632400740809)
  ·
    refine ⟨39275535827552724300555607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52367381103403632400740809 39275535827552724300555607)
    ·
      refine ⟨58913303741329086450833411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39275535827552724300555607 58913303741329086450833411)
      ·
        refine ⟨88369955611993629676250117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58913303741329086450833411 88369955611993629676250117)
        ·
          refine ⟨16569366677248805564296897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88369955611993629676250117 16569366677248805564296897)
          ·
            refine ⟨12427025007936604173222673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16569366677248805564296897 12427025007936604173222673)
            ·
              refine ⟨9320268755952453129917005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12427025007936604173222673 9320268755952453129917005)
              ·
                refine ⟨3495100783482169923718877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9320268755952453129917005 3495100783482169923718877)
                ·
                  refine ⟨1310662793805813721394579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3495100783482169923718877 1310662793805813721394579)
                  ·
                    refine ⟨1965994190708720582091869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1310662793805813721394579 1965994190708720582091869)
                    ·
                      refine ⟨737247821515770218284451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1965994190708720582091869 737247821515770218284451)
                      ·
                        rfl

theorem cell23_1435785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_1435785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435785 prefixEnd_1435785 := by exact prefixLift 1435785
  have htrace : WordTrace (prefixWord ++ tailWord_1435785) baseStart_1435785 baseEnd_1435785 := by
    simpa [prefixWord, tailWord_1435785, baseEnd_1435785] using wordTrace_append hprefix tailTrace_1435785
  have hstable : (prefixWord ++ tailWord_1435785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435785).length < 2 ^ (prefixWord ++ tailWord_1435785).sum := by decide
  have hdescent : baseEnd_1435785 < baseStart_1435785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435806 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1435806 : Nat := 118140960795 + 1435806 * 2 ^ 59
def prefixEnd_1435806 : Nat := 4983230072969 + 3 ^ 40 * 1435806 * 2
def baseEnd_1435806 : Nat := 737258604609514636121855

theorem tailTrace_1435806 : CollatzResearch.WordTrace tailWord_1435806 prefixEnd_1435806 737258604609514636121855 := by
  unfold tailWord_1435806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546018379540944123406909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34912098024218368658170181 6546018379540944123406909)
  ·
    refine ⟨2454756892327854046277591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6546018379540944123406909 2454756892327854046277591)
    ·
      refine ⟨3682135338491781069416387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454756892327854046277591 3682135338491781069416387)
      ·
        refine ⟨5523203007737671604124581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682135338491781069416387 5523203007737671604124581)
        ·
          refine ⟨1035600563950813425773359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5523203007737671604124581 1035600563950813425773359)
          ·
            refine ⟨1553400845926220138660039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035600563950813425773359 1553400845926220138660039)
            ·
              refine ⟨2330101268889330207990059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553400845926220138660039 2330101268889330207990059)
              ·
                refine ⟨3495151903333995311985089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330101268889330207990059 3495151903333995311985089)
                ·
                  refine ⟨2621363927500496483988817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495151903333995311985089 2621363927500496483988817)
                  ·
                    refine ⟨1966022945625372362991613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2621363927500496483988817 1966022945625372362991613)
                    ·
                      refine ⟨737258604609514636121855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966022945625372362991613 737258604609514636121855)
                      ·
                        rfl

theorem cell23_1435806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1435806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435806 prefixEnd_1435806 := by exact prefixLift 1435806
  have htrace : WordTrace (prefixWord ++ tailWord_1435806) baseStart_1435806 baseEnd_1435806 := by
    simpa [prefixWord, tailWord_1435806, baseEnd_1435806] using wordTrace_append hprefix tailTrace_1435806
  have hstable : (prefixWord ++ tailWord_1435806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435806).length < 2 ^ (prefixWord ++ tailWord_1435806).sum := by decide
  have hdescent : baseEnd_1435806 < baseStart_1435806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435812 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_1435812 : Nat := 118140960795 + 1435812 * 2 ^ 59
def prefixEnd_1435812 : Nat := 4983230072969 + 3 ^ 40 * 1435812 * 2
def baseEnd_1435812 : Nat := 737261685493441612646827

theorem tailTrace_1435812 : CollatzResearch.WordTrace tailWord_1435812 prefixEnd_1435812 737261685493441612646827 := by
  unfold tailWord_1435812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26184182937152908005986845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34912243916203877341315793 26184182937152908005986845)
  ·
    refine ⟨9819068601432340502245067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26184182937152908005986845 9819068601432340502245067)
    ·
      refine ⟨14728602902148510753367601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9819068601432340502245067 14728602902148510753367601)
      ·
        refine ⟨11046452176611383065025701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14728602902148510753367601 11046452176611383065025701)
        ·
          refine ⟨2071209783114634324692319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11046452176611383065025701 2071209783114634324692319)
          ·
            refine ⟨3106814674671951487038479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071209783114634324692319 3106814674671951487038479)
            ·
              refine ⟨4660222012007927230557719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106814674671951487038479 4660222012007927230557719)
              ·
                refine ⟨6990333018011890845836579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660222012007927230557719 6990333018011890845836579)
                ·
                  refine ⟨10485499527017836268754869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990333018011890845836579 10485499527017836268754869)
                  ·
                    refine ⟨983015580657922150195769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10485499527017836268754869 983015580657922150195769)
                    ·
                      refine ⟨737261685493441612646827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983015580657922150195769 737261685493441612646827)
                      ·
                        rfl

theorem cell23_1435812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_1435812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435812 prefixEnd_1435812 := by exact prefixLift 1435812
  have htrace : WordTrace (prefixWord ++ tailWord_1435812) baseStart_1435812 baseEnd_1435812 := by
    simpa [prefixWord, tailWord_1435812, baseEnd_1435812] using wordTrace_append hprefix tailTrace_1435812
  have hstable : (prefixWord ++ tailWord_1435812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435812).length < 2 ^ (prefixWord ++ tailWord_1435812).sum := by decide
  have hdescent : baseEnd_1435812 < baseStart_1435812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435935 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1435935 : Nat := 118140960795 + 1435935 * 2 ^ 59
def prefixEnd_1435935 : Nat := 4983230072969 + 3 ^ 40 * 1435935 * 2
def baseEnd_1435935 : Nat := 737324843613944631408761

theorem tailTrace_1435935 : CollatzResearch.WordTrace tailWord_1435935 prefixEnd_1435935 737324843613944631408761 := by
  unfold tailWord_1435935
  simp only [CollatzResearch.WordTrace]
  refine ⟨52372852052860208018701259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34915234701906805345800839 52372852052860208018701259)
  ·
    refine ⟨78559278079290312028051889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52372852052860208018701259 78559278079290312028051889)
    ·
      refine ⟨58919458559467734021038917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78559278079290312028051889 58919458559467734021038917)
      ·
        refine ⟨11047398479900200128944797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58919458559467734021038917 11047398479900200128944797)
        ·
          refine ⟨4142774429962575048354299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11047398479900200128944797 4142774429962575048354299)
          ·
            refine ⟨6214161644943862572531449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142774429962575048354299 6214161644943862572531449)
            ·
              refine ⟨4660621233707896929398587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214161644943862572531449 4660621233707896929398587)
              ·
                refine ⟨6990931850561845394097881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660621233707896929398587 6990931850561845394097881)
                ·
                  refine ⟨5243198887921384045573411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990931850561845394097881 5243198887921384045573411)
                  ·
                    refine ⟨7864798331882076068360117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243198887921384045573411 7864798331882076068360117)
                    ·
                      refine ⟨737324843613944631408761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7864798331882076068360117 737324843613944631408761)
                      ·
                        rfl

theorem cell23_1435935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1435935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435935 prefixEnd_1435935 := by exact prefixLift 1435935
  have htrace : WordTrace (prefixWord ++ tailWord_1435935) baseStart_1435935 baseEnd_1435935 := by
    simpa [prefixWord, tailWord_1435935, baseEnd_1435935] using wordTrace_append hprefix tailTrace_1435935
  have hstable : (prefixWord ++ tailWord_1435935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435935).length < 2 ^ (prefixWord ++ tailWord_1435935).sum := by decide
  have hdescent : baseEnd_1435935 < baseStart_1435935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435936 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1435936 : Nat := 118140960795 + 1435936 * 2 ^ 59
def prefixEnd_1435936 : Nat := 4983230072969 + 3 ^ 40 * 1435936 * 2
def baseEnd_1435936 : Nat := 737325357094599127496257

theorem tailTrace_1435936 : CollatzResearch.WordTrace tailWord_1435936 prefixEnd_1435936 737325357094599127496257 := by
  unfold tailWord_1435936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186444262928292594743831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34915259017237723459658441 26186444262928292594743831)
  ·
    refine ⟨39279666394392438892115747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26186444262928292594743831 39279666394392438892115747)
    ·
      refine ⟨58919499591588658338173621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39279666394392438892115747 58919499591588658338173621)
      ·
        refine ⟨5523703086711436719203777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58919499591588658338173621 5523703086711436719203777)
        ·
          refine ⟨4142777315033577539402833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523703086711436719203777 4142777315033577539402833)
          ·
            refine ⟨3107082986275183154552125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142777315033577539402833 3107082986275183154552125)
            ·
              refine ⟨1165156119853193682957047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3107082986275183154552125 1165156119853193682957047)
              ·
                refine ⟨1747734179779790524435571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165156119853193682957047 1747734179779790524435571)
                ·
                  refine ⟨2621601269669685786653357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747734179779790524435571 2621601269669685786653357)
                  ·
                    refine ⟨983100476126132169995009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621601269669685786653357 983100476126132169995009)
                    ·
                      refine ⟨737325357094599127496257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983100476126132169995009 737325357094599127496257)
                      ·
                        rfl

theorem cell23_1435936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1435936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435936 prefixEnd_1435936 := by exact prefixLift 1435936
  have htrace : WordTrace (prefixWord ++ tailWord_1435936) baseStart_1435936 baseEnd_1435936 := by
    simpa [prefixWord, tailWord_1435936, baseEnd_1435936] using wordTrace_append hprefix tailTrace_1435936
  have hstable : (prefixWord ++ tailWord_1435936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435936).length < 2 ^ (prefixWord ++ tailWord_1435936).sum := by decide
  have hdescent : baseEnd_1435936 < baseStart_1435936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435948 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1435948 : Nat := 118140960795 + 1435948 * 2 ^ 59
def prefixEnd_1435948 : Nat := 4983230072969 + 3 ^ 40 * 1435948 * 2
def baseEnd_1435948 : Nat := 737331518862453080546201

theorem tailTrace_1435948 : CollatzResearch.WordTrace tailWord_1435948 prefixEnd_1435948 737331518862453080546201 := by
  unfold tailWord_1435948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186663100906555619462249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34915550801208740825949665 26186663100906555619462249)
  ·
    refine ⟨19639997325679916714596687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26186663100906555619462249 19639997325679916714596687)
    ·
      refine ⟨29459995988519875071895031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19639997325679916714596687 29459995988519875071895031)
      ·
        refine ⟨44189993982779812607842547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29459995988519875071895031 44189993982779812607842547)
        ·
          refine ⟨66284990974169718911763821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44189993982779812607842547 66284990974169718911763821)
          ·
            refine ⟨24856871615313644591911433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66284990974169718911763821 24856871615313644591911433)
            ·
              refine ⟨18642653711485233443933575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24856871615313644591911433 18642653711485233443933575)
              ·
                refine ⟨27963980567227850165900363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18642653711485233443933575 27963980567227850165900363)
                ·
                  refine ⟨41945970850841775248850545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27963980567227850165900363 41945970850841775248850545)
                  ·
                    refine ⟨31459478138131331436637909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41945970850841775248850545 31459478138131331436637909)
                    ·
                      refine ⟨737331518862453080546201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31459478138131331436637909 737331518862453080546201)
                      ·
                        rfl

theorem cell23_1435948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1435948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435948 prefixEnd_1435948 := by exact prefixLift 1435948
  have htrace : WordTrace (prefixWord ++ tailWord_1435948) baseStart_1435948 baseEnd_1435948 := by
    simpa [prefixWord, tailWord_1435948, baseEnd_1435948] using wordTrace_append hprefix tailTrace_1435948
  have hstable : (prefixWord ++ tailWord_1435948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435948).length < 2 ^ (prefixWord ++ tailWord_1435948).sum := by decide
  have hdescent : baseEnd_1435948 < baseStart_1435948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435966 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_1435966 : Nat := 118140960795 + 1435966 * 2 ^ 59
def prefixEnd_1435966 : Nat := 4983230072969 + 3 ^ 40 * 1435966 * 2
def baseEnd_1435966 : Nat := 737340761514234010121119

theorem tailTrace_1435966 : CollatzResearch.WordTrace tailWord_1435966 prefixEnd_1435966 737340761514234010121119 := by
  unfold tailWord_1435966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546747839468487539134969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34915988477165266875386501 6546747839468487539134969)
  ·
    refine ⟨4910060879601365654351227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6546747839468487539134969 4910060879601365654351227)
    ·
      refine ⟨7365091319402048481526841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910060879601365654351227 7365091319402048481526841)
      ·
        refine ⟨5523818489551536361145131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365091319402048481526841 5523818489551536361145131)
        ·
          refine ⟨8285727734327304541717697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523818489551536361145131 8285727734327304541717697)
          ·
            refine ⟨6214295800745478406288273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285727734327304541717697 6214295800745478406288273)
            ·
              refine ⟨4660721850559108804716205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214295800745478406288273 4660721850559108804716205)
              ·
                refine ⟨1747770693959665801768577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4660721850559108804716205 1747770693959665801768577)
                ·
                  refine ⟨1310828020469749351326433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747770693959665801768577 1310828020469749351326433)
                  ·
                    refine ⟨983121015352312013494825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1310828020469749351326433 983121015352312013494825)
                    ·
                      refine ⟨737340761514234010121119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983121015352312013494825 737340761514234010121119)
                      ·
                        rfl

theorem cell23_1435966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_1435966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435966 prefixEnd_1435966 := by exact prefixLift 1435966
  have htrace : WordTrace (prefixWord ++ tailWord_1435966) baseStart_1435966 baseEnd_1435966 := by
    simpa [prefixWord, tailWord_1435966, baseEnd_1435966] using wordTrace_append hprefix tailTrace_1435966
  have hstable : (prefixWord ++ tailWord_1435966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435966).length < 2 ^ (prefixWord ++ tailWord_1435966).sum := by decide
  have hdescent : baseEnd_1435966 < baseStart_1435966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435985 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_1435985 : Nat := 118140960795 + 1435985 * 2 ^ 59
def prefixEnd_1435985 : Nat := 4983230072969 + 3 ^ 40 * 1435985 * 2
def baseEnd_1435985 : Nat := 245783505882223145261177

theorem tailTrace_1435985 : CollatzResearch.WordTrace tailWord_1435985 prefixEnd_1435985 245783505882223145261177 := by
  unfold tailWord_1435985
  simp only [CollatzResearch.WordTrace]
  refine ⟨52374675702679066558021409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34916450468452711038680939 52374675702679066558021409)
  ·
    refine ⟨39281006777009299918516057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52374675702679066558021409 39281006777009299918516057)
    ·
      refine ⟨29460755082756974938887043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39281006777009299918516057 29460755082756974938887043)
      ·
        refine ⟨44191132624135462408330565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29460755082756974938887043 44191132624135462408330565)
        ·
          refine ⟨8285837367025399201561981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44191132624135462408330565 8285837367025399201561981)
          ·
            refine ⟨3107189012634524700585743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8285837367025399201561981 3107189012634524700585743)
            ·
              refine ⟨4660783518951787050878615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107189012634524700585743 4660783518951787050878615)
              ·
                refine ⟨6991175278427680576317923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660783518951787050878615 6991175278427680576317923)
                ·
                  refine ⟨10486762917641520864476885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6991175278427680576317923 10486762917641520864476885)
                  ·
                    refine ⟨245783505882223145261177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10486762917641520864476885 245783505882223145261177)
                    ·
                      rfl

theorem cell23_1435985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_1435985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435985 prefixEnd_1435985 := by exact prefixLift 1435985
  have htrace : WordTrace (prefixWord ++ tailWord_1435985) baseStart_1435985 baseEnd_1435985 := by
    simpa [prefixWord, tailWord_1435985, baseEnd_1435985] using wordTrace_append hprefix tailTrace_1435985
  have hstable : (prefixWord ++ tailWord_1435985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435985).length < 2 ^ (prefixWord ++ tailWord_1435985).sum := by decide
  have hdescent : baseEnd_1435985 < baseStart_1435985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435989 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 5]
def baseStart_1435989 : Nat := 118140960795 + 1435989 * 2 ^ 59
def prefixEnd_1435989 : Nat := 4983230072969 + 3 ^ 40 * 1435989 * 2
def baseEnd_1435989 : Nat := 81928063507698602237057

theorem tailTrace_1435989 : CollatzResearch.WordTrace tailWord_1435989 prefixEnd_1435989 81928063507698602237057 := by
  unfold tailWord_1435989
  simp only [CollatzResearch.WordTrace]
  refine ⟨52374821594664575241167021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34916547729776383494111347 52374821594664575241167021)
  ·
    refine ⟨19640558097999215715437633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52374821594664575241167021 19640558097999215715437633)
    ·
      refine ⟨14730418573499411786578225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19640558097999215715437633 14730418573499411786578225)
      ·
        refine ⟨11047813930124558839933669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14730418573499411786578225 11047813930124558839933669)
        ·
          refine ⟨2071465111898354782487563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11047813930124558839933669 2071465111898354782487563)
          ·
            refine ⟨3107197667847532173731345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071465111898354782487563 3107197667847532173731345)
            ·
              refine ⟨2330398250885649130298509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107197667847532173731345 2330398250885649130298509)
              ·
                refine ⟨873899344082118423861941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2330398250885649130298509 873899344082118423861941)
                ·
                  refine ⟨81928063507698602237057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 873899344082118423861941 81928063507698602237057)
                  ·
                    rfl

theorem cell23_1435989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_1435989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1435989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1435989 prefixEnd_1435989 := by exact prefixLift 1435989
  have htrace : WordTrace (prefixWord ++ tailWord_1435989) baseStart_1435989 baseEnd_1435989 := by
    simpa [prefixWord, tailWord_1435989, baseEnd_1435989] using wordTrace_append hprefix tailTrace_1435989
  have hstable : (prefixWord ++ tailWord_1435989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435989).length < 2 ^ (prefixWord ++ tailWord_1435989).sum := by decide
  have hdescent : baseEnd_1435989 < baseStart_1435989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436105 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_1436105 : Nat := 118140960795 + 1436105 * 2 ^ 59
def prefixEnd_1436105 : Nat := 4983230072969 + 3 ^ 40 * 1436105 * 2
def baseEnd_1436105 : Nat := 245804045108402988760993

theorem tailTrace_1436105 : CollatzResearch.WordTrace tailWord_1436105 prefixEnd_1436105 245804045108402988760993 := by
  unfold tailWord_1436105
  simp only [CollatzResearch.WordTrace]
  refine ⟨52379052462244327052389769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34919368308162884701593179 52379052462244327052389769)
  ·
    refine ⟨39284289346683245289292327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52379052462244327052389769 39284289346683245289292327)
    ·
      refine ⟨58926434020024867933938491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39284289346683245289292327 58926434020024867933938491)
      ·
        refine ⟨88389651030037301900907737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58926434020024867933938491 88389651030037301900907737)
        ·
          refine ⟨66292238272527976425680803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88389651030037301900907737 66292238272527976425680803)
          ·
            refine ⟨99438357408791964638521205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66292238272527976425680803 99438357408791964638521205)
            ·
              refine ⟨9322346007074246684861363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99438357408791964638521205 9322346007074246684861363)
              ·
                refine ⟨13983519010611370027292045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322346007074246684861363 13983519010611370027292045)
                ·
                  refine ⟨5243819628979263760234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13983519010611370027292045 5243819628979263760234517)
                  ·
                    refine ⟨245804045108402988760993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5243819628979263760234517 245804045108402988760993)
                    ·
                      rfl

theorem cell23_1436105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_1436105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436105 prefixEnd_1436105 := by exact prefixLift 1436105
  have htrace : WordTrace (prefixWord ++ tailWord_1436105) baseStart_1436105 baseEnd_1436105 := by
    simpa [prefixWord, tailWord_1436105, baseEnd_1436105] using wordTrace_append hprefix tailTrace_1436105
  have hstable : (prefixWord ++ tailWord_1436105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436105).length < 2 ^ (prefixWord ++ tailWord_1436105).sum := by decide
  have hdescent : baseEnd_1436105 < baseStart_1436105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436106 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_1436106 : Nat := 118140960795 + 1436106 * 2 ^ 59
def prefixEnd_1436106 : Nat := 4983230072969 + 3 ^ 40 * 1436106 * 2
def baseEnd_1436106 : Nat := 737412648805863462370475

theorem tailTrace_1436106 : CollatzResearch.WordTrace tailWord_1436106 prefixEnd_1436106 737412648805863462370475 := by
  unfold tailWord_1436106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094772233810176055794043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34919392623493802815450781 13094772233810176055794043)
  ·
    refine ⟨19642158350715264083691065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094772233810176055794043 19642158350715264083691065)
    ·
      refine ⟨14731618763036448062768299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19642158350715264083691065 14731618763036448062768299)
      ·
        refine ⟨22097428144554672094152449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731618763036448062768299 22097428144554672094152449)
        ·
          refine ⟨16573071108416004070614337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22097428144554672094152449 16573071108416004070614337)
          ·
            refine ⟨12429803331312003052960753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16573071108416004070614337 12429803331312003052960753)
            ·
              refine ⟨9322352498484002289720565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12429803331312003052960753 9322352498484002289720565)
              ·
                refine ⟨873970546732875214661303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9322352498484002289720565 873970546732875214661303)
                ·
                  refine ⟨1310955820099312821991955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873970546732875214661303 1310955820099312821991955)
                  ·
                    refine ⟨1966433730148969232987933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1310955820099312821991955 1966433730148969232987933)
                    ·
                      refine ⟨737412648805863462370475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966433730148969232987933 737412648805863462370475)
                      ·
                        rfl

theorem cell23_1436106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_1436106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436106 prefixEnd_1436106 := by exact prefixLift 1436106
  have htrace : WordTrace (prefixWord ++ tailWord_1436106) baseStart_1436106 baseEnd_1436106 := by
    simpa [prefixWord, tailWord_1436106, baseEnd_1436106] using wordTrace_append hprefix tailTrace_1436106
  have hstable : (prefixWord ++ tailWord_1436106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436106).length < 2 ^ (prefixWord ++ tailWord_1436106).sum := by decide
  have hdescent : baseEnd_1436106 < baseStart_1436106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436116 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1436116 : Nat := 118140960795 + 1436116 * 2 ^ 59
def prefixEnd_1436116 : Nat := 4983230072969 + 3 ^ 40 * 1436116 * 2
def baseEnd_1436116 : Nat := 737417783612408423245429

theorem tailTrace_1436116 : CollatzResearch.WordTrace tailWord_1436116 prefixEnd_1436116 737417783612408423245429 := by
  unfold tailWord_1436116
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189726832602237965520101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34919635776802983954026801 26189726832602237965520101)
  ·
    refine ⟨4910573781112919618535019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26189726832602237965520101 4910573781112919618535019)
    ·
      refine ⟨7365860671669379427802529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910573781112919618535019 7365860671669379427802529)
      ·
        refine ⟨5524395503752034570851897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365860671669379427802529 5524395503752034570851897)
        ·
          refine ⟨4143296627814025928138923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5524395503752034570851897 4143296627814025928138923)
          ·
            refine ⟨6214944941721038892208385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143296627814025928138923 6214944941721038892208385)
            ·
              refine ⟨4661208706290779169156289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214944941721038892208385 4661208706290779169156289)
              ·
                refine ⟨3495906529718084376867217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661208706290779169156289 3495906529718084376867217)
                ·
                  refine ⟨2621929897288563282650413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495906529718084376867217 2621929897288563282650413)
                  ·
                    refine ⟨983223711483211230993905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621929897288563282650413 983223711483211230993905)
                    ·
                      refine ⟨737417783612408423245429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983223711483211230993905 737417783612408423245429)
                      ·
                        rfl

theorem cell23_1436116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1436116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436116 prefixEnd_1436116 := by exact prefixLift 1436116
  have htrace : WordTrace (prefixWord ++ tailWord_1436116) baseStart_1436116 baseEnd_1436116 := by
    simpa [prefixWord, tailWord_1436116, baseEnd_1436116] using wordTrace_append hprefix tailTrace_1436116
  have hstable : (prefixWord ++ tailWord_1436116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436116).length < 2 ^ (prefixWord ++ tailWord_1436116).sum := by decide
  have hdescent : baseEnd_1436116 < baseStart_1436116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436152 : List Nat := [2, 1, 2, 1, 1, 4, 5, 7]
def baseStart_1436152 : Nat := 118140960795 + 1436152 * 2 ^ 59
def prefixEnd_1436152 : Nat := 4983230072969 + 3 ^ 40 * 1436152 * 2
def baseEnd_1436152 : Nat := 27312454404295195644269

theorem tailTrace_1436152 : CollatzResearch.WordTrace tailWord_1436152 prefixEnd_1436152 27312454404295195644269 := by
  unfold tailWord_1436152
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190383346537027039675355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34920511128716036052900473 26190383346537027039675355)
  ·
    refine ⟨39285575019805540559513033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26190383346537027039675355 39285575019805540559513033)
    ·
      refine ⟨29464181264854155419634775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39285575019805540559513033 29464181264854155419634775)
      ·
        refine ⟨44196271897281233129452163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29464181264854155419634775 44196271897281233129452163)
        ·
          refine ⟨66294407845921849694178245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44196271897281233129452163 66294407845921849694178245)
          ·
            refine ⟨12430201471110346817658421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66294407845921849694178245 12430201471110346817658421)
            ·
              refine ⟨1165331387916595014155477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12430201471110346817658421 1165331387916595014155477)
              ·
                refine ⟨27312454404295195644269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1165331387916595014155477 27312454404295195644269)
                ·
                  rfl

theorem cell23_1436152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 7].length) (baseStart_1436152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436152 prefixEnd_1436152 := by exact prefixLift 1436152
  have htrace : WordTrace (prefixWord ++ tailWord_1436152) baseStart_1436152 baseEnd_1436152 := by
    simpa [prefixWord, tailWord_1436152, baseEnd_1436152] using wordTrace_append hprefix tailTrace_1436152
  have hstable : (prefixWord ++ tailWord_1436152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436152).length < 2 ^ (prefixWord ++ tailWord_1436152).sum := by decide
  have hdescent : baseEnd_1436152 < baseStart_1436152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436163 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 1, 2, 2]
def baseStart_1436163 : Nat := 118140960795 + 1436163 * 2 ^ 59
def prefixEnd_1436163 : Nat := 4983230072969 + 3 ^ 40 * 1436163 * 2
def baseEnd_1436163 : Nat := 737441917203169739357713

theorem tailTrace_1436163 : CollatzResearch.WordTrace tailWord_1436163 prefixEnd_1436163 737441917203169739357713 := by
  unfold tailWord_1436163
  simp only [CollatzResearch.WordTrace]
  refine ⟨52381167896034202958001143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34920778597356135305334095 52381167896034202958001143)
  ·
    refine ⟨78571751844051304437001715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52381167896034202958001143 78571751844051304437001715)
    ·
      refine ⟨117857627766076956655502573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78571751844051304437001715 117857627766076956655502573)
      ·
        refine ⟨44196610412278858745813465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117857627766076956655502573 44196610412278858745813465)
        ·
          refine ⟨33147457809209144059360099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44196610412278858745813465 33147457809209144059360099)
          ·
            refine ⟨49721186713813716089040149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33147457809209144059360099 49721186713813716089040149)
            ·
              refine ⟨2330680627210017941673757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49721186713813716089040149 2330680627210017941673757)
              ·
                refine ⟨874005235203756728127659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2330680627210017941673757 874005235203756728127659)
                ·
                  refine ⟨1311007852805635092191489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874005235203756728127659 1311007852805635092191489)
                  ·
                    refine ⟨983255889604226319143617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311007852805635092191489 983255889604226319143617)
                    ·
                      refine ⟨737441917203169739357713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983255889604226319143617 737441917203169739357713)
                      ·
                        rfl

theorem cell23_1436163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_1436163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436163 prefixEnd_1436163 := by exact prefixLift 1436163
  have htrace : WordTrace (prefixWord ++ tailWord_1436163) baseStart_1436163 baseEnd_1436163 := by
    simpa [prefixWord, tailWord_1436163, baseEnd_1436163] using wordTrace_append hprefix tailTrace_1436163
  have hstable : (prefixWord ++ tailWord_1436163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436163).length < 2 ^ (prefixWord ++ tailWord_1436163).sum := by decide
  have hdescent : baseEnd_1436163 < baseStart_1436163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436173 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1436173 : Nat := 118140960795 + 1436173 * 2 ^ 59
def prefixEnd_1436173 : Nat := 4983230072969 + 3 ^ 40 * 1436173 * 2
def baseEnd_1436173 : Nat := 245815684003238233410889

theorem tailTrace_1436173 : CollatzResearch.WordTrace tailWord_1436173 prefixEnd_1436173 245815684003238233410889 := by
  unfold tailWord_1436173
  simp only [CollatzResearch.WordTrace]
  refine ⟨52381532625997974665865173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34921021750665316443910115 52381532625997974665865173)
  ·
    refine ⟨1227692170921827531231215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 52381532625997974665865173 1227692170921827531231215)
    ·
      refine ⟨1841538256382741296846823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227692170921827531231215 1841538256382741296846823)
      ·
        refine ⟨2762307384574111945270235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841538256382741296846823 2762307384574111945270235)
        ·
          refine ⟨4143461076861167917905353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762307384574111945270235 4143461076861167917905353)
          ·
            refine ⟨3107595807645875938429015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4143461076861167917905353 3107595807645875938429015)
            ·
              refine ⟨4661393711468813907643523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107595807645875938429015 4661393711468813907643523)
              ·
                refine ⟨6992090567203220861465285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661393711468813907643523 6992090567203220861465285)
                ·
                  refine ⟨1311016981350603911524741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6992090567203220861465285 1311016981350603911524741)
                  ·
                    refine ⟨245815684003238233410889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311016981350603911524741 245815684003238233410889)
                    ·
                      rfl

theorem cell23_1436173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1436173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436173 prefixEnd_1436173 := by exact prefixLift 1436173
  have htrace : WordTrace (prefixWord ++ tailWord_1436173) baseStart_1436173 baseEnd_1436173 := by
    simpa [prefixWord, tailWord_1436173, baseEnd_1436173] using wordTrace_append hprefix tailTrace_1436173
  have hstable : (prefixWord ++ tailWord_1436173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436173).length < 2 ^ (prefixWord ++ tailWord_1436173).sum := by decide
  have hdescent : baseEnd_1436173 < baseStart_1436173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436179 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 3]
def baseStart_1436179 : Nat := 118140960795 + 1436179 * 2 ^ 59
def prefixEnd_1436179 : Nat := 4983230072969 + 3 ^ 40 * 1436179 * 2
def baseEnd_1436179 : Nat := 737450132893641676757639

theorem tailTrace_1436179 : CollatzResearch.WordTrace tailWord_1436179 prefixEnd_1436179 737450132893641676757639 := by
  unfold tailWord_1436179
  simp only [CollatzResearch.WordTrace]
  refine ⟨52381751463976237690583591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34921167642650825127055727 52381751463976237690583591)
  ·
    refine ⟨78572627195964356535875387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52381751463976237690583591 78572627195964356535875387)
    ·
      refine ⟨117858940793946534803813081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78572627195964356535875387 117858940793946534803813081)
      ·
        refine ⟨88394205595459901102859811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117858940793946534803813081 88394205595459901102859811)
        ·
          refine ⟨132591308393189851654289717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88394205595459901102859811 132591308393189851654289717)
          ·
            refine ⟨12430435161861548592589661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132591308393189851654289717 12430435161861548592589661)
            ·
              refine ⟨4661413185698080722221123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12430435161861548592589661 4661413185698080722221123)
              ·
                refine ⟨6992119778547121083331685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661413185698080722221123 6992119778547121083331685)
                ·
                  refine ⟨1311022458477585203124691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6992119778547121083331685 1311022458477585203124691)
                  ·
                    refine ⟨1966533687716377804687037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311022458477585203124691 1966533687716377804687037)
                    ·
                      refine ⟨737450132893641676757639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966533687716377804687037 737450132893641676757639)
                      ·
                        rfl

theorem cell23_1436179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_1436179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436179 prefixEnd_1436179 := by exact prefixLift 1436179
  have htrace : WordTrace (prefixWord ++ tailWord_1436179) baseStart_1436179 baseEnd_1436179 := by
    simpa [prefixWord, tailWord_1436179, baseEnd_1436179] using wordTrace_append hprefix tailTrace_1436179
  have hstable : (prefixWord ++ tailWord_1436179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436179).length < 2 ^ (prefixWord ++ tailWord_1436179).sum := by decide
  have hdescent : baseEnd_1436179 < baseStart_1436179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436180 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1436180 : Nat := 118140960795 + 1436180 * 2 ^ 59
def prefixEnd_1436180 : Nat := 4983230072969 + 3 ^ 40 * 1436180 * 2
def baseEnd_1436180 : Nat := 737450646374296172845135

theorem tailTrace_1436180 : CollatzResearch.WordTrace tailWord_1436180 prefixEnd_1436180 737450646374296172845135 := by
  unfold tailWord_1436180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190893968486307430684997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34921191957981743240913329 26190893968486307430684997)
  ·
    refine ⟨4910792619091182643253437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26190893968486307430684997 4910792619091182643253437)
    ·
      refine ⟨1841547232159193491220039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4910792619091182643253437 1841547232159193491220039)
      ·
        refine ⟨2762320848238790236830059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841547232159193491220039 2762320848238790236830059)
        ·
          refine ⟨4143481272358185355245089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762320848238790236830059 4143481272358185355245089)
          ·
            refine ⟨3107610954268639016433817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4143481272358185355245089 3107610954268639016433817)
            ·
              refine ⟨2330708215701479262325363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107610954268639016433817 2330708215701479262325363)
              ·
                refine ⟨3496062323552218893488045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330708215701479262325363 3496062323552218893488045)
                ·
                  refine ⟨1311023371332082085058017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496062323552218893488045 1311023371332082085058017)
                  ·
                    refine ⟨983267528499061563793513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311023371332082085058017 983267528499061563793513)
                    ·
                      refine ⟨737450646374296172845135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983267528499061563793513 737450646374296172845135)
                      ·
                        rfl

theorem cell23_1436180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1436180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436180 prefixEnd_1436180 := by exact prefixLift 1436180
  have htrace : WordTrace (prefixWord ++ tailWord_1436180) baseStart_1436180 baseEnd_1436180 := by
    simpa [prefixWord, tailWord_1436180, baseEnd_1436180] using wordTrace_append hprefix tailTrace_1436180
  have hstable : (prefixWord ++ tailWord_1436180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436180).length < 2 ^ (prefixWord ++ tailWord_1436180).sum := by decide
  have hdescent : baseEnd_1436180 < baseStart_1436180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436232 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1436232 : Nat := 118140960795 + 1436232 * 2 ^ 59
def prefixEnd_1436232 : Nat := 4983230072969 + 3 ^ 40 * 1436232 * 2
def baseEnd_1436232 : Nat := 737477347368329969394895

theorem tailTrace_1436232 : CollatzResearch.WordTrace tailWord_1436232 prefixEnd_1436232 737477347368329969394895 := by
  unfold tailWord_1436232
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191842266392113871131475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34922456355189485161508633 26191842266392113871131475)
  ·
    refine ⟨39287763399588170806697213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26191842266392113871131475 39287763399588170806697213)
    ·
      refine ⟨14732911274845564052511455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39287763399588170806697213 14732911274845564052511455)
      ·
        refine ⟨22099366912268346078767183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14732911274845564052511455 22099366912268346078767183)
        ·
          refine ⟨33149050368402519118150775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22099366912268346078767183 33149050368402519118150775)
          ·
            refine ⟨49723575552603778677226163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33149050368402519118150775 49723575552603778677226163)
            ·
              refine ⟨74585363328905668015839245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49723575552603778677226163 74585363328905668015839245)
              ·
                refine ⟨27969511248339625505939717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74585363328905668015839245 27969511248339625505939717)
                ·
                  refine ⟨5244283359063679782363697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27969511248339625505939717 5244283359063679782363697)
                  ·
                    refine ⟨3933212519297759836772773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5244283359063679782363697 3933212519297759836772773)
                    ·
                      refine ⟨737477347368329969394895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3933212519297759836772773 737477347368329969394895)
                      ·
                        rfl

theorem cell23_1436232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1436232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436232 prefixEnd_1436232 := by exact prefixLift 1436232
  have htrace : WordTrace (prefixWord ++ tailWord_1436232) baseStart_1436232 baseEnd_1436232 := by
    simpa [prefixWord, tailWord_1436232, baseEnd_1436232] using wordTrace_append hprefix tailTrace_1436232
  have hstable : (prefixWord ++ tailWord_1436232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436232).length < 2 ^ (prefixWord ++ tailWord_1436232).sum := by decide
  have hdescent : baseEnd_1436232 < baseStart_1436232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436236 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1436236 : Nat := 118140960795 + 1436236 * 2 ^ 59
def prefixEnd_1436236 : Nat := 4983230072969 + 3 ^ 40 * 1436236 * 2
def baseEnd_1436236 : Nat := 737479401290947953744877

theorem tailTrace_1436236 : CollatzResearch.WordTrace tailWord_1436236 prefixEnd_1436236 737479401290947953744877 := by
  unfold tailWord_1436236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191915212384868212704281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34922553616513157616939041 26191915212384868212704281)
  ·
    refine ⟨19643936409288651159528211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26191915212384868212704281 19643936409288651159528211)
    ·
      refine ⟨29465904613932976739292317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19643936409288651159528211 29465904613932976739292317)
      ·
        refine ⟨11049714230224866277234619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29465904613932976739292317 11049714230224866277234619)
        ·
          refine ⟨16574571345337299415851929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11049714230224866277234619 16574571345337299415851929)
          ·
            refine ⟨12430928509002974561888947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16574571345337299415851929 12430928509002974561888947)
            ·
              refine ⟨18646392763504461842833421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12430928509002974561888947 18646392763504461842833421)
              ·
                refine ⟨6992397286314173191062533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18646392763504461842833421 6992397286314173191062533)
                ·
                  refine ⟨1311074491183907473324225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6992397286314173191062533 1311074491183907473324225)
                  ·
                    refine ⟨983305868387930604993169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311074491183907473324225 983305868387930604993169)
                    ·
                      refine ⟨737479401290947953744877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983305868387930604993169 737479401290947953744877)
                      ·
                        rfl

theorem cell23_1436236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1436236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436236 prefixEnd_1436236 := by exact prefixLift 1436236
  have htrace : WordTrace (prefixWord ++ tailWord_1436236) baseStart_1436236 baseEnd_1436236 := by
    simpa [prefixWord, tailWord_1436236, baseEnd_1436236] using wordTrace_append hprefix tailTrace_1436236
  have hstable : (prefixWord ++ tailWord_1436236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436236).length < 2 ^ (prefixWord ++ tailWord_1436236).sum := by decide
  have hdescent : baseEnd_1436236 < baseStart_1436236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436289 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1436289 : Nat := 118140960795 + 1436289 * 2 ^ 59
def prefixEnd_1436289 : Nat := 4983230072969 + 3 ^ 40 * 1436289 * 2
def baseEnd_1436289 : Nat := 245835538588545415460711

theorem tailTrace_1436289 : CollatzResearch.WordTrace tailWord_1436289 prefixEnd_1436289 245835538588545415460711 := by
  unfold tailWord_1436289
  simp only [CollatzResearch.WordTrace]
  refine ⟨52385763493577726477087921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34923842329051817651391947 52385763493577726477087921)
  ·
    refine ⟨39289322620183294857815941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52385763493577726477087921 39289322620183294857815941)
    ·
      refine ⟨7366747991284367785840489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39289322620183294857815941 7366747991284367785840489)
      ·
        refine ⟨5525060993463275839380367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366747991284367785840489 5525060993463275839380367)
        ·
          refine ⟨8287591490194913759070551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525060993463275839380367 8287591490194913759070551)
          ·
            refine ⟨12431387235292370638605827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287591490194913759070551 12431387235292370638605827)
            ·
              refine ⟨18647080852938555957908741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431387235292370638605827 18647080852938555957908741)
              ·
                refine ⟨3496327659925979242107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18647080852938555957908741 3496327659925979242107889)
                ·
                  refine ⟨2622245744944484431580917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3496327659925979242107889 2622245744944484431580917)
                  ·
                    refine ⟨245835538588545415460711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2622245744944484431580917 245835538588545415460711)
                    ·
                      rfl

theorem cell23_1436289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1436289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436289 prefixEnd_1436289 := by exact prefixLift 1436289
  have htrace : WordTrace (prefixWord ++ tailWord_1436289) baseStart_1436289 baseEnd_1436289 := by
    simpa [prefixWord, tailWord_1436289, baseEnd_1436289] using wordTrace_append hprefix tailTrace_1436289
  have hstable : (prefixWord ++ tailWord_1436289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436289).length < 2 ^ (prefixWord ++ tailWord_1436289).sum := by decide
  have hdescent : baseEnd_1436289 < baseStart_1436289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436293 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 5]
def baseStart_1436293 : Nat := 118140960795 + 1436293 * 2 ^ 59
def prefixEnd_1436293 : Nat := 4983230072969 + 3 ^ 40 * 1436293 * 2
def baseEnd_1436293 : Nat := 81945407743139358970235

theorem tailTrace_1436293 : CollatzResearch.WordTrace tailWord_1436293 prefixEnd_1436293 81945407743139358970235 := by
  unfold tailWord_1436293
  simp only [CollatzResearch.WordTrace]
  refine ⟨52385909385563235160233533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34923939590375490106822355 52385909385563235160233533)
  ·
    refine ⟨19644716019586213185087575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52385909385563235160233533 19644716019586213185087575)
    ·
      refine ⟨29467074029379319777631363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644716019586213185087575 29467074029379319777631363)
      ·
        refine ⟨44200611044068979666447045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29467074029379319777631363 44200611044068979666447045)
        ·
          refine ⟨8287614570762933687458821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44200611044068979666447045 8287614570762933687458821)
          ·
            refine ⟨1553927732018050066398529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8287614570762933687458821 1553927732018050066398529)
            ·
              refine ⟨1165445799013537549798897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553927732018050066398529 1165445799013537549798897)
              ·
                refine ⟨874084349260153162349173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165445799013537549798897 874084349260153162349173)
                ·
                  refine ⟨81945407743139358970235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874084349260153162349173 81945407743139358970235)
                  ·
                    rfl

theorem cell23_1436293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_1436293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436293 prefixEnd_1436293 := by exact prefixLift 1436293
  have htrace : WordTrace (prefixWord ++ tailWord_1436293) baseStart_1436293 baseEnd_1436293 := by
    simpa [prefixWord, tailWord_1436293, baseEnd_1436293] using wordTrace_append hprefix tailTrace_1436293
  have hstable : (prefixWord ++ tailWord_1436293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436293).length < 2 ^ (prefixWord ++ tailWord_1436293).sum := by decide
  have hdescent : baseEnd_1436293 < baseStart_1436293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436349 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 8]
def baseStart_1436349 : Nat := 118140960795 + 1436349 * 2 ^ 59
def prefixEnd_1436349 : Nat := 4983230072969 + 3 ^ 40 * 1436349 * 2
def baseEnd_1436349 : Nat := 81948602733878445736873

theorem tailTrace_1436349 : CollatzResearch.WordTrace tailWord_1436349 prefixEnd_1436349 81948602733878445736873 := by
  unfold tailWord_1436349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52387951873360356724272101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34925301248906904482848067 52387951873360356724272101)
  ·
    refine ⟨9822740976255066885801019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52387951873360356724272101 9822740976255066885801019)
    ·
      refine ⟨14734111464382600328701529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9822740976255066885801019 14734111464382600328701529)
      ·
        refine ⟨11050583598286950246526147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14734111464382600328701529 11050583598286950246526147)
        ·
          refine ⟨16575875397430425369789221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050583598286950246526147 16575875397430425369789221)
          ·
            refine ⟨3107976637018204756835479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16575875397430425369789221 3107976637018204756835479)
            ·
              refine ⟨4661964955527307135253219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107976637018204756835479 4661964955527307135253219)
              ·
                refine ⟨6992947433290960702879829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661964955527307135253219 6992947433290960702879829)
                ·
                  refine ⟨81948602733878445736873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6992947433290960702879829 81948602733878445736873)
                  ·
                    rfl

theorem cell23_1436349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_1436349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436349 prefixEnd_1436349 := by exact prefixLift 1436349
  have htrace : WordTrace (prefixWord ++ tailWord_1436349) baseStart_1436349 baseEnd_1436349 := by
    simpa [prefixWord, tailWord_1436349, baseEnd_1436349] using wordTrace_append hprefix tailTrace_1436349
  have hstable : (prefixWord ++ tailWord_1436349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436349).length < 2 ^ (prefixWord ++ tailWord_1436349).sum := by decide
  have hdescent : baseEnd_1436349 < baseStart_1436349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436404 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1436404 : Nat := 118140960795 + 1436404 * 2 ^ 59
def prefixEnd_1436404 : Nat := 4983230072969 + 3 ^ 40 * 1436404 * 2
def baseEnd_1436404 : Nat := 245855222013634432148035

theorem tailTrace_1436404 : CollatzResearch.WordTrace tailWord_1436404 prefixEnd_1436404 245855222013634432148035 := by
  unfold tailWord_1436404
  simp only [CollatzResearch.WordTrace]
  refine ⟨26194978944080550558762133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34926638592107400745016177 26194978944080550558762133)
  ·
    refine ⟨1227889638003775807441975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26194978944080550558762133 1227889638003775807441975)
    ·
      refine ⟨1841834457005663711162963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227889638003775807441975 1841834457005663711162963)
      ·
        refine ⟨2762751685508495566744445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841834457005663711162963 2762751685508495566744445)
        ·
          refine ⟨1036031882065685837529167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762751685508495566744445 1036031882065685837529167)
          ·
            refine ⟨1554047823098528756293751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036031882065685837529167 1554047823098528756293751)
            ·
              refine ⟨2331071734647793134440627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554047823098528756293751 2331071734647793134440627)
              ·
                refine ⟨3496607601971689701660941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331071734647793134440627 3496607601971689701660941)
                ·
                  refine ⟨1311227850739383638122853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496607601971689701660941 1311227850739383638122853)
                  ·
                    refine ⟨245855222013634432148035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311227850739383638122853 245855222013634432148035)
                    ·
                      rfl

theorem cell23_1436404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1436404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436404 prefixEnd_1436404 := by exact prefixLift 1436404
  have htrace : WordTrace (prefixWord ++ tailWord_1436404) baseStart_1436404 baseEnd_1436404 := by
    simpa [prefixWord, tailWord_1436404, baseEnd_1436404] using wordTrace_append hprefix tailTrace_1436404
  have hstable : (prefixWord ++ tailWord_1436404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436404).length < 2 ^ (prefixWord ++ tailWord_1436404).sum := by decide
  have hdescent : baseEnd_1436404 < baseStart_1436404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436419 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3]
def baseStart_1436419 : Nat := 118140960795 + 1436419 * 2 ^ 59
def prefixEnd_1436419 : Nat := 4983230072969 + 3 ^ 40 * 1436419 * 2
def baseEnd_1436419 : Nat := 737573368250720737756535

theorem tailTrace_1436419 : CollatzResearch.WordTrace tailWord_1436419 prefixEnd_1436419 737573368250720737756535 := by
  unfold tailWord_1436419
  simp only [CollatzResearch.WordTrace]
  refine ⟨52390504983106758679320311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34927003322071172452880207 52390504983106758679320311)
  ·
    refine ⟨78585757474660138018980467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52390504983106758679320311 78585757474660138018980467)
    ·
      refine ⟨117878636211990207028470701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78585757474660138018980467 117878636211990207028470701)
      ·
        refine ⟨44204488579496327635676513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117878636211990207028470701 44204488579496327635676513)
        ·
          refine ⟨33153366434622245726757385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44204488579496327635676513 33153366434622245726757385)
          ·
            refine ⟨24865024825966684295068039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33153366434622245726757385 24865024825966684295068039)
            ·
              refine ⟨37297537238950026442602059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24865024825966684295068039 37297537238950026442602059)
              ·
                refine ⟨55946305858425039663903089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37297537238950026442602059 55946305858425039663903089)
                ·
                  refine ⟨41959729393818779747927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55946305858425039663903089 41959729393818779747927317)
                  ·
                    refine ⟨1966862315335255300684093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41959729393818779747927317 1966862315335255300684093)
                    ·
                      refine ⟨737573368250720737756535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966862315335255300684093 737573368250720737756535)
                      ·
                        rfl

theorem cell23_1436419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1436419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436419 prefixEnd_1436419 := by exact prefixLift 1436419
  have htrace : WordTrace (prefixWord ++ tailWord_1436419) baseStart_1436419 baseEnd_1436419 := by
    simpa [prefixWord, tailWord_1436419, baseEnd_1436419] using wordTrace_append hprefix tailTrace_1436419
  have hstable : (prefixWord ++ tailWord_1436419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436419).length < 2 ^ (prefixWord ++ tailWord_1436419).sum := by decide
  have hdescent : baseEnd_1436419 < baseStart_1436419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436433 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_1436433 : Nat := 118140960795 + 1436433 * 2 ^ 59
def prefixEnd_1436433 : Nat := 4983230072969 + 3 ^ 40 * 1436433 * 2
def baseEnd_1436433 : Nat := 737580556979883682981471

theorem tailTrace_1436433 : CollatzResearch.WordTrace tailWord_1436433 prefixEnd_1436433 737580556979883682981471 := by
  unfold tailWord_1436433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52391015605056039070329953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34927343736704026046886635 52391015605056039070329953)
  ·
    refine ⟨39293261703792029302747465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52391015605056039070329953 39293261703792029302747465)
    ·
      refine ⟨29469946277844021977060599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39293261703792029302747465 29469946277844021977060599)
      ·
        refine ⟨44204919416766032965590899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29469946277844021977060599 44204919416766032965590899)
        ·
          refine ⟨66307379125149049448386349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44204919416766032965590899 66307379125149049448386349)
          ·
            refine ⟨24865267171930893543144881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66307379125149049448386349 24865267171930893543144881)
            ·
              refine ⟨18648950378948170157358661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24865267171930893543144881 18648950378948170157358661)
              ·
                refine ⟨3496678196052781904504749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18648950378948170157358661 3496678196052781904504749)
                ·
                  refine ⟨1311254323519793214189281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496678196052781904504749 1311254323519793214189281)
                  ·
                    refine ⟨983440742639844910641961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311254323519793214189281 983440742639844910641961)
                    ·
                      refine ⟨737580556979883682981471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983440742639844910641961 737580556979883682981471)
                      ·
                        rfl

theorem cell23_1436433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_1436433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436433 prefixEnd_1436433 := by exact prefixLift 1436433
  have htrace : WordTrace (prefixWord ++ tailWord_1436433) baseStart_1436433 baseEnd_1436433 := by
    simpa [prefixWord, tailWord_1436433, baseEnd_1436433] using wordTrace_append hprefix tailTrace_1436433
  have hstable : (prefixWord ++ tailWord_1436433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436433).length < 2 ^ (prefixWord ++ tailWord_1436433).sum := by decide
  have hdescent : baseEnd_1436433 < baseStart_1436433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436450 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_1436450 : Nat := 118140960795 + 1436450 * 2 ^ 59
def prefixEnd_1436450 : Nat := 4983230072969 + 3 ^ 40 * 1436450 * 2
def baseEnd_1436450 : Nat := 737589286151010116468893

theorem tailTrace_1436450 : CollatzResearch.WordTrace tailWord_1436450 prefixEnd_1436450 737589286151010116468893 := by
  unfold tailWord_1436450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097908911498612743424701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34927757097329633982465869 13097908911498612743424701)
  ·
    refine ⟨4911715841811979778784263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13097908911498612743424701 4911715841811979778784263)
    ·
      refine ⟨7367573762717969668176395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4911715841811979778784263 7367573762717969668176395)
      ·
        refine ⟨11051360644076954502264593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367573762717969668176395 11051360644076954502264593)
        ·
          refine ⟨8288520483057715876698445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11051360644076954502264593 8288520483057715876698445)
          ·
            refine ⟨3108195181146643453761917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8288520483057715876698445 3108195181146643453761917)
            ·
              refine ⟨1165573192929991295160719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108195181146643453761917 1165573192929991295160719)
              ·
                refine ⟨1748359789394986942741079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165573192929991295160719 1748359789394986942741079)
                ·
                  refine ⟨2622539684092480414111619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748359789394986942741079 2622539684092480414111619)
                  ·
                    refine ⟨3933809526138720621167429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2622539684092480414111619 3933809526138720621167429)
                    ·
                      refine ⟨737589286151010116468893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3933809526138720621167429 737589286151010116468893)
                      ·
                        rfl

theorem cell23_1436450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_1436450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436450 prefixEnd_1436450 := by exact prefixLift 1436450
  have htrace : WordTrace (prefixWord ++ tailWord_1436450) baseStart_1436450 baseEnd_1436450 := by
    simpa [prefixWord, tailWord_1436450, baseEnd_1436450] using wordTrace_append hprefix tailTrace_1436450
  have hstable : (prefixWord ++ tailWord_1436450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436450).length < 2 ^ (prefixWord ++ tailWord_1436450).sum := by decide
  have hdescent : baseEnd_1436450 < baseStart_1436450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436466 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1436466 : Nat := 118140960795 + 1436466 * 2 ^ 59
def prefixEnd_1436466 : Nat := 4983230072969 + 3 ^ 40 * 1436466 * 2
def baseEnd_1436466 : Nat := 737597501841482053868819

theorem tailTrace_1436466 : CollatzResearch.WordTrace tailWord_1436466 prefixEnd_1436466 737597501841482053868819 := by
  unfold tailWord_1436466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098054803484121426570313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34928146142624323804187501 13098054803484121426570313)
  ·
    refine ⟨9823541102613091069927735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13098054803484121426570313 9823541102613091069927735)
    ·
      refine ⟨14735311653919636604891603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9823541102613091069927735 14735311653919636604891603)
      ·
        refine ⟨22102967480879454907337405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14735311653919636604891603 22102967480879454907337405)
        ·
          refine ⟨8288612805329795590251527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22102967480879454907337405 8288612805329795590251527)
          ·
            refine ⟨12432919207994693385377291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288612805329795590251527 12432919207994693385377291)
            ·
              refine ⟨18649378811992040078065937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432919207994693385377291 18649378811992040078065937)
              ·
                refine ⟨13987034108994030058549453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18649378811992040078065937 13987034108994030058549453)
                ·
                  refine ⟨5245137790872761271956045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13987034108994030058549453 5245137790872761271956045)
                  ·
                    refine ⟨1966926671577285476983517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5245137790872761271956045 1966926671577285476983517)
                    ·
                      refine ⟨737597501841482053868819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966926671577285476983517 737597501841482053868819)
                      ·
                        rfl

theorem cell23_1436466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1436466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436466 prefixEnd_1436466 := by exact prefixLift 1436466
  have htrace : WordTrace (prefixWord ++ tailWord_1436466) baseStart_1436466 baseEnd_1436466 := by
    simpa [prefixWord, tailWord_1436466, baseEnd_1436466] using wordTrace_append hprefix tailTrace_1436466
  have hstable : (prefixWord ++ tailWord_1436466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436466).length < 2 ^ (prefixWord ++ tailWord_1436466).sum := by decide
  have hdescent : baseEnd_1436466 < baseStart_1436466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436467 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 1, 2, 2]
def baseStart_1436467 : Nat := 118140960795 + 1436467 * 2 ^ 59
def prefixEnd_1436467 : Nat := 4983230072969 + 3 ^ 40 * 1436467 * 2
def baseEnd_1436467 : Nat := 737598015322136549956315

theorem tailTrace_1436467 : CollatzResearch.WordTrace tailWord_1436467 prefixEnd_1436467 737598015322136549956315 := by
  unfold tailWord_1436467
  simp only [CollatzResearch.WordTrace]
  refine ⟨52392255686932862877067655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34928170457955241918045103 52392255686932862877067655)
  ·
    refine ⟨78588383530399294315601483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52392255686932862877067655 78588383530399294315601483)
    ·
      refine ⟨117882575295598941473402225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78588383530399294315601483 117882575295598941473402225)
      ·
        refine ⟨88411931471699206105051669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117882575295598941473402225 88411931471699206105051669)
        ·
          refine ⟨4144309287735900286174297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88411931471699206105051669 4144309287735900286174297)
          ·
            refine ⟨3108231965801925214630723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144309287735900286174297 3108231965801925214630723)
            ·
              refine ⟨4662347948702887821946085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108231965801925214630723 4662347948702887821946085)
              ·
                refine ⟨874190240381791466614891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4662347948702887821946085 874190240381791466614891)
                ·
                  refine ⟨1311285360572687199922337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874190240381791466614891 1311285360572687199922337)
                  ·
                    refine ⟨983464020429515399941753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311285360572687199922337 983464020429515399941753)
                    ·
                      refine ⟨737598015322136549956315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983464020429515399941753 737598015322136549956315)
                      ·
                        rfl

theorem cell23_1436467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 2, 2].length) (baseStart_1436467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436467 prefixEnd_1436467 := by exact prefixLift 1436467
  have htrace : WordTrace (prefixWord ++ tailWord_1436467) baseStart_1436467 baseEnd_1436467 := by
    simpa [prefixWord, tailWord_1436467, baseEnd_1436467] using wordTrace_append hprefix tailTrace_1436467
  have hstable : (prefixWord ++ tailWord_1436467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436467).length < 2 ^ (prefixWord ++ tailWord_1436467).sum := by decide
  have hdescent : baseEnd_1436467 < baseStart_1436467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436483 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 3]
def baseStart_1436483 : Nat := 118140960795 + 1436483 * 2 ^ 59
def prefixEnd_1436483 : Nat := 4983230072969 + 3 ^ 40 * 1436483 * 2
def baseEnd_1436483 : Nat := 737606231012608487356241

theorem tailTrace_1436483 : CollatzResearch.WordTrace tailWord_1436483 prefixEnd_1436483 737606231012608487356241 := by
  unfold tailWord_1436483
  simp only [CollatzResearch.WordTrace]
  refine ⟨52392839254874897609650103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34928559503249931739766735 52392839254874897609650103)
  ·
    refine ⟨78589258882312346414475155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52392839254874897609650103 78589258882312346414475155)
    ·
      refine ⟨117883888323468519621712733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78589258882312346414475155 117883888323468519621712733)
      ·
        refine ⟨44206458121300694858142275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117883888323468519621712733 44206458121300694858142275)
        ·
          refine ⟨66309687181951042287213413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44206458121300694858142275 66309687181951042287213413)
          ·
            refine ⟨12433066346615820428852515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66309687181951042287213413 12433066346615820428852515)
            ·
              refine ⟨18649599519923730643278773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433066346615820428852515 18649599519923730643278773)
              ·
                refine ⟨1748399954992849747807385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18649599519923730643278773 1748399954992849747807385)
                ·
                  refine ⟨1311299966244637310855539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748399954992849747807385 1311299966244637310855539)
                  ·
                    refine ⟨1966949949366955966283309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311299966244637310855539 1966949949366955966283309)
                    ·
                      refine ⟨737606231012608487356241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1966949949366955966283309 737606231012608487356241)
                      ·
                        rfl

theorem cell23_1436483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_1436483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436483 prefixEnd_1436483 := by exact prefixLift 1436483
  have htrace : WordTrace (prefixWord ++ tailWord_1436483) baseStart_1436483 baseEnd_1436483 := by
    simpa [prefixWord, tailWord_1436483, baseEnd_1436483] using wordTrace_append hprefix tailTrace_1436483
  have hstable : (prefixWord ++ tailWord_1436483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436483).length < 2 ^ (prefixWord ++ tailWord_1436483).sum := by decide
  have hdescent : baseEnd_1436483 < baseStart_1436483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436484 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1436484 : Nat := 118140960795 + 1436484 * 2 ^ 59
def prefixEnd_1436484 : Nat := 4983230072969 + 3 ^ 40 * 1436484 * 2
def baseEnd_1436484 : Nat := 737606744493262983443737

theorem tailTrace_1436484 : CollatzResearch.WordTrace tailWord_1436484 prefixEnd_1436484 737606744493262983443737 := by
  unfold tailWord_1436484
  simp only [CollatzResearch.WordTrace]
  refine ⟨26196437863935637390218253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34928583818580849853624337 26196437863935637390218253)
  ·
    refine ⟨9823664198975864021331845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26196437863935637390218253 9823664198975864021331845)
    ·
      refine ⟨1841937037307974503999721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9823664198975864021331845 1841937037307974503999721)
      ·
        refine ⟨1381452777980980877999791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841937037307974503999721 1381452777980980877999791)
        ·
          refine ⟨2072179166971471316999687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381452777980980877999791 2072179166971471316999687)
          ·
            refine ⟨3108268750457206975499531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072179166971471316999687 3108268750457206975499531)
            ·
              refine ⟨4662403125685810463249297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108268750457206975499531 4662403125685810463249297)
              ·
                refine ⟨3496802344264357847436973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662403125685810463249297 3496802344264357847436973)
                ·
                  refine ⟨1311300879099134192788865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496802344264357847436973 1311300879099134192788865)
                  ·
                    refine ⟨983475659324350644591649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311300879099134192788865 983475659324350644591649)
                    ·
                      refine ⟨737606744493262983443737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983475659324350644591649 737606744493262983443737)
                      ·
                        rfl

theorem cell23_1436484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1436484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436484 prefixEnd_1436484 := by exact prefixLift 1436484
  have htrace : WordTrace (prefixWord ++ tailWord_1436484) baseStart_1436484 baseEnd_1436484 := by
    simpa [prefixWord, tailWord_1436484, baseEnd_1436484] using wordTrace_append hprefix tailTrace_1436484
  have hstable : (prefixWord ++ tailWord_1436484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436484).length < 2 ^ (prefixWord ++ tailWord_1436484).sum := by decide
  have hdescent : baseEnd_1436484 < baseStart_1436484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436516 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1436516 : Nat := 118140960795 + 1436516 * 2 ^ 59
def prefixEnd_1436516 : Nat := 4983230072969 + 3 ^ 40 * 1436516 * 2
def baseEnd_1436516 : Nat := 245874391958068952747863

theorem tailTrace_1436516 : CollatzResearch.WordTrace tailWord_1436516 prefixEnd_1436516 245874391958068952747863 := by
  unfold tailWord_1436516
  simp only [CollatzResearch.WordTrace]
  refine ⟨26197021431877672122800701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34929361909170229497067601 26197021431877672122800701)
  ·
    refine ⟨9823883036954127046050263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26197021431877672122800701 9823883036954127046050263)
    ·
      refine ⟨14735824555431190569075395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9823883036954127046050263 14735824555431190569075395)
      ·
        refine ⟨22103736833146785853613093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14735824555431190569075395 22103736833146785853613093)
        ·
          refine ⟨4144450656215022347552455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22103736833146785853613093 4144450656215022347552455)
          ·
            refine ⟨6216675984322533521328683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4144450656215022347552455 6216675984322533521328683)
            ·
              refine ⟨9325013976483800281993025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216675984322533521328683 9325013976483800281993025)
              ·
                refine ⟨6993760482362850211494769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9325013976483800281993025 6993760482362850211494769)
                ·
                  refine ⟨5245320361772137658621077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993760482362850211494769 5245320361772137658621077)
                  ·
                    refine ⟨245874391958068952747863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5245320361772137658621077 245874391958068952747863)
                    ·
                      rfl

theorem cell23_1436516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1436516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436516 prefixEnd_1436516 := by exact prefixLift 1436516
  have htrace : WordTrace (prefixWord ++ tailWord_1436516) baseStart_1436516 baseEnd_1436516 := by
    simpa [prefixWord, tailWord_1436516, baseEnd_1436516] using wordTrace_append hprefix tailTrace_1436516
  have hstable : (prefixWord ++ tailWord_1436516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436516).length < 2 ^ (prefixWord ++ tailWord_1436516).sum := by decide
  have hdescent : baseEnd_1436516 < baseStart_1436516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436534 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1436534 : Nat := 118140960795 + 1436534 * 2 ^ 59
def prefixEnd_1436534 : Nat := 4983230072969 + 3 ^ 40 * 1436534 * 2
def baseEnd_1436534 : Nat := 737632418525987787818507

theorem tailTrace_1436534 : CollatzResearch.WordTrace tailWord_1436534 prefixEnd_1436534 737632418525987787818507 := by
  unfold tailWord_1436534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274668711105633332484791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34929799585126755546504437 3274668711105633332484791)
  ·
    refine ⟨4912003066658449998727187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274668711105633332484791 4912003066658449998727187)
    ·
      refine ⟨7368004599987674998090781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912003066658449998727187 7368004599987674998090781)
      ·
        refine ⟨2763001724995378124284043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7368004599987674998090781 2763001724995378124284043)
        ·
          refine ⟨4144502587493067186426065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763001724995378124284043 4144502587493067186426065)
          ·
            refine ⟨3108376940619800389819549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144502587493067186426065 3108376940619800389819549)
            ·
              refine ⟨1165641352732425146182331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108376940619800389819549 1165641352732425146182331)
              ·
                refine ⟨1748462029098637719273497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165641352732425146182331 1748462029098637719273497)
                ·
                  refine ⟨1311346521823978289455123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748462029098637719273497 1311346521823978289455123)
                  ·
                    refine ⟨1967019782735967434182685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311346521823978289455123 1967019782735967434182685)
                    ·
                      refine ⟨737632418525987787818507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967019782735967434182685 737632418525987787818507)
                      ·
                        rfl

theorem cell23_1436534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1436534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436534 prefixEnd_1436534 := by exact prefixLift 1436534
  have htrace : WordTrace (prefixWord ++ tailWord_1436534) baseStart_1436534 baseEnd_1436534 := by
    simpa [prefixWord, tailWord_1436534, baseEnd_1436534] using wordTrace_append hprefix tailTrace_1436534
  have hstable : (prefixWord ++ tailWord_1436534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436534).length < 2 ^ (prefixWord ++ tailWord_1436534).sum := by decide
  have hdescent : baseEnd_1436534 < baseStart_1436534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436540 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_1436540 : Nat := 118140960795 + 1436540 * 2 ^ 59
def prefixEnd_1436540 : Nat := 4983230072969 + 3 ^ 40 * 1436540 * 2
def baseEnd_1436540 : Nat := 737635499409914764343479

theorem tailTrace_1436540 : CollatzResearch.WordTrace tailWord_1436540 prefixEnd_1436540 737635499409914764343479 := by
  unfold tailWord_1436540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26197459107834198172237537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34929945477112264229650049 26197459107834198172237537)
  ·
    refine ⟨19648094330875648629178153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26197459107834198172237537 19648094330875648629178153)
    ·
      refine ⟨14736070748156736471883615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19648094330875648629178153 14736070748156736471883615)
      ·
        refine ⟨22104106122235104707825423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14736070748156736471883615 22104106122235104707825423)
        ·
          refine ⟨33156159183352657061738135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22104106122235104707825423 33156159183352657061738135)
          ·
            refine ⟨49734238775028985592607203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33156159183352657061738135 49734238775028985592607203)
            ·
              refine ⟨74601358162543478388910805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49734238775028985592607203 74601358162543478388910805)
              ·
                refine ⟨1748469331934612774740097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74601358162543478388910805 1748469331934612774740097)
                ·
                  refine ⟨1311351998950959581055073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748469331934612774740097 1311351998950959581055073)
                  ·
                    refine ⟨983513999213219685791305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311351998950959581055073 983513999213219685791305)
                    ·
                      refine ⟨737635499409914764343479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983513999213219685791305 737635499409914764343479)
                      ·
                        rfl

theorem cell23_1436540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_1436540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436540 prefixEnd_1436540 := by exact prefixLift 1436540
  have htrace : WordTrace (prefixWord ++ tailWord_1436540) baseStart_1436540 baseEnd_1436540 := by
    simpa [prefixWord, tailWord_1436540, baseEnd_1436540] using wordTrace_append hprefix tailTrace_1436540
  have hstable : (prefixWord ++ tailWord_1436540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436540).length < 2 ^ (prefixWord ++ tailWord_1436540).sum := by decide
  have hdescent : baseEnd_1436540 < baseStart_1436540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436556 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1436556 : Nat := 118140960795 + 1436556 * 2 ^ 59
def prefixEnd_1436556 : Nat := 4983230072969 + 3 ^ 40 * 1436556 * 2
def baseEnd_1436556 : Nat := 737643715100386701743405

theorem tailTrace_1436556 : CollatzResearch.WordTrace tailWord_1436556 prefixEnd_1436556 737643715100386701743405 := by
  unfold tailWord_1436556
  simp only [CollatzResearch.WordTrace]
  refine ⟨26197750891805215538528761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34930334522406954051371681 26197750891805215538528761)
  ·
    refine ⟨19648313168853911653896571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26197750891805215538528761 19648313168853911653896571)
    ·
      refine ⟨29472469753280867480844857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19648313168853911653896571 29472469753280867480844857)
      ·
        refine ⟨22104352314960650610633643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29472469753280867480844857 22104352314960650610633643)
        ·
          refine ⟨33156528472440975915950465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22104352314960650610633643 33156528472440975915950465)
          ·
            refine ⟨24867396354330731936962849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33156528472440975915950465 24867396354330731936962849)
            ·
              refine ⟨18650547265748048952722137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24867396354330731936962849 18650547265748048952722137)
              ·
                refine ⟨13987910449311036714541603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18650547265748048952722137 13987910449311036714541603)
                ·
                  refine ⟨20981865673966555071812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13987910449311036714541603 20981865673966555071812405)
                  ·
                    refine ⟨1967049906934364537982413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20981865673966555071812405 1967049906934364537982413)
                    ·
                      refine ⟨737643715100386701743405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967049906934364537982413 737643715100386701743405)
                      ·
                        rfl

theorem cell23_1436556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1436556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436556 prefixEnd_1436556 := by exact prefixLift 1436556
  have htrace : WordTrace (prefixWord ++ tailWord_1436556) baseStart_1436556 baseEnd_1436556 := by
    simpa [prefixWord, tailWord_1436556, baseEnd_1436556] using wordTrace_append hprefix tailTrace_1436556
  have hstable : (prefixWord ++ tailWord_1436556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436556).length < 2 ^ (prefixWord ++ tailWord_1436556).sum := by decide
  have hdescent : baseEnd_1436556 < baseStart_1436556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436576 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_1436576 : Nat := 118140960795 + 1436576 * 2 ^ 59
def prefixEnd_1436576 : Nat := 4983230072969 + 3 ^ 40 * 1436576 * 2
def baseEnd_1436576 : Nat := 245884661571158874497771

theorem tailTrace_1436576 : CollatzResearch.WordTrace tailWord_1436576 prefixEnd_1436576 245884661571158874497771 := by
  unfold tailWord_1436576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26198115621768987246392791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34930820829025316328523721 26198115621768987246392791)
  ·
    refine ⟨39297173432653480869589187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26198115621768987246392791 39297173432653480869589187)
    ·
      refine ⟨58945760148980221304383781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39297173432653480869589187 58945760148980221304383781)
      ·
        refine ⟨11052330027933791494571959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58945760148980221304383781 11052330027933791494571959)
        ·
          refine ⟨16578495041900687241857939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052330027933791494571959 16578495041900687241857939)
          ·
            refine ⟨24867742562851030862786909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16578495041900687241857939 24867742562851030862786909)
            ·
              refine ⟨9325403461069136573545091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24867742562851030862786909 9325403461069136573545091)
              ·
                refine ⟨13988105191603704860317637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9325403461069136573545091 13988105191603704860317637)
                ·
                  refine ⟨2622769723425694661309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13988105191603704860317637 2622769723425694661309557)
                  ·
                    refine ⟨245884661571158874497771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2622769723425694661309557 245884661571158874497771)
                    ·
                      rfl

theorem cell23_1436576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_1436576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436576 prefixEnd_1436576 := by exact prefixLift 1436576
  have htrace : WordTrace (prefixWord ++ tailWord_1436576) baseStart_1436576 baseEnd_1436576 := by
    simpa [prefixWord, tailWord_1436576, baseEnd_1436576] using wordTrace_append hprefix tailTrace_1436576
  have hstable : (prefixWord ++ tailWord_1436576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436576).length < 2 ^ (prefixWord ++ tailWord_1436576).sum := by decide
  have hdescent : baseEnd_1436576 < baseStart_1436576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436580 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1436580 : Nat := 118140960795 + 1436580 * 2 ^ 59
def prefixEnd_1436580 : Nat := 4983230072969 + 3 ^ 40 * 1436580 * 2
def baseEnd_1436580 : Nat := 81961782070677178649255

theorem tailTrace_1436580 : CollatzResearch.WordTrace tailWord_1436580 prefixEnd_1436580 81961782070677178649255 := by
  unfold tailWord_1436580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26198188567761741587965597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34930918090348988783954129 26198188567761741587965597)
  ·
    refine ⟨9824320712910653095487099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26198188567761741587965597 9824320712910653095487099)
    ·
      refine ⟨14736481069365979643230649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9824320712910653095487099 14736481069365979643230649)
      ·
        refine ⟨11052360802024484732422987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14736481069365979643230649 11052360802024484732422987)
        ·
          refine ⟨16578541203036727098634481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052360802024484732422987 16578541203036727098634481)
          ·
            refine ⟨12433905902277545323975861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16578541203036727098634481 12433905902277545323975861)
            ·
              refine ⟨1165678678338519874122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12433905902277545323975861 1165678678338519874122737)
              ·
                refine ⟨874259008753889905592053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165678678338519874122737 874259008753889905592053)
                ·
                  refine ⟨81961782070677178649255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874259008753889905592053 81961782070677178649255)
                  ·
                    rfl

theorem cell23_1436580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1436580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436580 prefixEnd_1436580 := by exact prefixLift 1436580
  have htrace : WordTrace (prefixWord ++ tailWord_1436580) baseStart_1436580 baseEnd_1436580 := by
    simpa [prefixWord, tailWord_1436580, baseEnd_1436580] using wordTrace_append hprefix tailTrace_1436580
  have hstable : (prefixWord ++ tailWord_1436580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436580).length < 2 ^ (prefixWord ++ tailWord_1436580).sum := by decide
  have hdescent : baseEnd_1436580 < baseStart_1436580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436697 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 1, 1, 3]
def baseStart_1436697 : Nat := 118140960795 + 1436697 * 2 ^ 59
def prefixEnd_1436697 : Nat := 4983230072969 + 3 ^ 40 * 1436697 * 2
def baseEnd_1436697 : Nat := 737716115872670650080257

theorem tailTrace_1436697 : CollatzResearch.WordTrace tailWord_1436697 prefixEnd_1436697 737716115872670650080257 := by
  unfold tailWord_1436697
  simp only [CollatzResearch.WordTrace]
  refine ⟨52400644476099612157940345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34933762984066408105293563 52400644476099612157940345)
  ·
    refine ⟨39300483357074709118455259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52400644476099612157940345 39300483357074709118455259)
    ·
      refine ⟨58950725035612063677682889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39300483357074709118455259 58950725035612063677682889)
      ·
        refine ⟨44213043776709047758262167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58950725035612063677682889 44213043776709047758262167)
        ·
          refine ⟨66319565665063571637393251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44213043776709047758262167 66319565665063571637393251)
          ·
            refine ⟨99479348497595357456089877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66319565665063571637393251 99479348497595357456089877)
            ·
              refine ⟨4663094460824782380754213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99479348497595357456089877 4663094460824782380754213)
              ·
                refine ⟨874330211404646696391415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4663094460824782380754213 874330211404646696391415)
                ·
                  refine ⟨1311495317106970044587123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874330211404646696391415 1311495317106970044587123)
                  ·
                    refine ⟨1967242975660455066880685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311495317106970044587123 1967242975660455066880685)
                    ·
                      refine ⟨737716115872670650080257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967242975660455066880685 737716115872670650080257)
                      ·
                        rfl

theorem cell23_1436697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_1436697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436697 prefixEnd_1436697 := by exact prefixLift 1436697
  have htrace : WordTrace (prefixWord ++ tailWord_1436697) baseStart_1436697 baseEnd_1436697 := by
    simpa [prefixWord, tailWord_1436697, baseEnd_1436697] using wordTrace_append hprefix tailTrace_1436697
  have hstable : (prefixWord ++ tailWord_1436697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436697).length < 2 ^ (prefixWord ++ tailWord_1436697).sum := by decide
  have hdescent : baseEnd_1436697 < baseStart_1436697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436720 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_1436720 : Nat := 118140960795 + 1436720 * 2 ^ 59
def prefixEnd_1436720 : Nat := 4983230072969 + 3 ^ 40 * 1436720 * 2
def baseEnd_1436720 : Nat := 737727925927724060092651

theorem tailTrace_1436720 : CollatzResearch.WordTrace tailWord_1436720 prefixEnd_1436720 737727925927724060092651 := by
  unfold tailWord_1436720
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200741677508143543013807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34934322236677524724018409 26200741677508143543013807)
  ·
    refine ⟨39301112516262215314520711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26200741677508143543013807 39301112516262215314520711)
    ·
      refine ⟨58951668774393322971781067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39301112516262215314520711 58951668774393322971781067)
      ·
        refine ⟨88427503161589984457671601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58951668774393322971781067 88427503161589984457671601)
        ·
          refine ⟨66320627371192488343253701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88427503161589984457671601 66320627371192488343253701)
          ·
            refine ⟨12435117632098591564360069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66320627371192488343253701 12435117632098591564360069)
            ·
              refine ⟨2331584556018485918317513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12435117632098591564360069 2331584556018485918317513)
              ·
                refine ⟨1748688417013864438738135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331584556018485918317513 1748688417013864438738135)
                ·
                  refine ⟨2623032625520796658107203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748688417013864438738135 2623032625520796658107203)
                  ·
                    refine ⟨3934548938281194987160805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623032625520796658107203 3934548938281194987160805)
                    ·
                      refine ⟨737727925927724060092651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3934548938281194987160805 737727925927724060092651)
                      ·
                        rfl

theorem cell23_1436720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_1436720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436720 prefixEnd_1436720 := by exact prefixLift 1436720
  have htrace : WordTrace (prefixWord ++ tailWord_1436720) baseStart_1436720 baseEnd_1436720 := by
    simpa [prefixWord, tailWord_1436720, baseEnd_1436720] using wordTrace_append hprefix tailTrace_1436720
  have hstable : (prefixWord ++ tailWord_1436720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436720).length < 2 ^ (prefixWord ++ tailWord_1436720).sum := by decide
  have hdescent : baseEnd_1436720 < baseStart_1436720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436743 : List Nat := [1, 1, 4, 1, 3, 4, 9]
def baseStart_1436743 : Nat := 118140960795 + 1436743 * 2 ^ 59
def prefixEnd_1436743 : Nat := 4983230072969 + 3 ^ 40 * 1436743 * 2
def baseEnd_1436743 : Nat := 9107897975096018149445

theorem tailTrace_1436743 : CollatzResearch.WordTrace tailWord_1436743 prefixEnd_1436743 9107897975096018149445 := by
  unfold tailWord_1436743
  simp only [CollatzResearch.WordTrace]
  refine ⟨52402322233932962014114883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34934881489288641342743255 52402322233932962014114883)
  ·
    refine ⟨78603483350899443021172325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52402322233932962014114883 78603483350899443021172325)
    ·
      refine ⟨14738153128293645566469811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78603483350899443021172325 14738153128293645566469811)
      ·
        refine ⟨22107229692440468349704717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14738153128293645566469811 22107229692440468349704717)
        ·
          refine ⟨8290211134665175631139269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22107229692440468349704717 8290211134665175631139269)
          ·
            refine ⟨1554414587749720430838613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8290211134665175631139269 1554414587749720430838613)
            ·
              refine ⟨9107897975096018149445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1554414587749720430838613 9107897975096018149445)
              ·
                rfl

theorem cell23_1436743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 9].length) (baseStart_1436743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436743 prefixEnd_1436743 := by exact prefixLift 1436743
  have htrace : WordTrace (prefixWord ++ tailWord_1436743) baseStart_1436743 baseEnd_1436743 := by
    simpa [prefixWord, tailWord_1436743, baseEnd_1436743] using wordTrace_append hprefix tailTrace_1436743
  have hstable : (prefixWord ++ tailWord_1436743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436743).length < 2 ^ (prefixWord ++ tailWord_1436743).sum := by decide
  have hdescent : baseEnd_1436743 < baseStart_1436743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436754 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_1436754 : Nat := 118140960795 + 1436754 * 2 ^ 59
def prefixEnd_1436754 : Nat := 4983230072969 + 3 ^ 40 * 1436754 * 2
def baseEnd_1436754 : Nat := 737745384269976927067495

theorem tailTrace_1436754 : CollatzResearch.WordTrace tailWord_1436754 prefixEnd_1436754 737745384269976927067495 := by
  unfold tailWord_1436754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100680859223277723191329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34935148957928740595176877 13100680859223277723191329)
  ·
    refine ⟨9825510644417458292393497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13100680859223277723191329 9825510644417458292393497)
    ·
      refine ⟨7369132983313093719295123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9825510644417458292393497 7369132983313093719295123)
      ·
        refine ⟨11053699474969640578942685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369132983313093719295123 11053699474969640578942685)
        ·
          refine ⟨4145137303113615217103507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11053699474969640578942685 4145137303113615217103507)
          ·
            refine ⟨6217705954670422825655261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145137303113615217103507 6217705954670422825655261)
            ·
              refine ⟨2331639733001408559620723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6217705954670422825655261 2331639733001408559620723)
              ·
                refine ⟨3497459599502112839431085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331639733001408559620723 3497459599502112839431085)
                ·
                  refine ⟨1311547349813292314786657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3497459599502112839431085 1311547349813292314786657)
                  ·
                    refine ⟨983660512359969236089993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311547349813292314786657 983660512359969236089993)
                    ·
                      refine ⟨737745384269976927067495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983660512359969236089993 737745384269976927067495)
                      ·
                        rfl

theorem cell23_1436754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_1436754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436754 prefixEnd_1436754 := by exact prefixLift 1436754
  have htrace : WordTrace (prefixWord ++ tailWord_1436754) baseStart_1436754 baseEnd_1436754 := by
    simpa [prefixWord, tailWord_1436754, baseEnd_1436754] using wordTrace_append hprefix tailTrace_1436754
  have hstable : (prefixWord ++ tailWord_1436754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436754).length < 2 ^ (prefixWord ++ tailWord_1436754).sum := by decide
  have hdescent : baseEnd_1436754 < baseStart_1436754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436798 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1436798 : Nat := 118140960795 + 1436798 * 2 ^ 59
def prefixEnd_1436798 : Nat := 4983230072969 + 3 ^ 40 * 1436798 * 2
def baseEnd_1436798 : Nat := 245922659139591584972431

theorem tailTrace_1436798 : CollatzResearch.WordTrace tailWord_1436798 prefixEnd_1436798 245922659139591584972431 := by
  unfold tailWord_1436798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550541031091713300920881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34936218832489137604911365 6550541031091713300920881)
  ·
    refine ⟨4912905773318784975690661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6550541031091713300920881 4912905773318784975690661)
    ·
      refine ⟨921169832497272182941999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4912905773318784975690661 921169832497272182941999)
      ·
        refine ⟨1381754748745908274412999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921169832497272182941999 1381754748745908274412999)
        ·
          refine ⟨2072632123118862411619499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381754748745908274412999 2072632123118862411619499)
          ·
            refine ⟨3108948184678293617429249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072632123118862411619499 3108948184678293617429249)
            ·
              refine ⟨2331711138508720213071937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108948184678293617429249 2331711138508720213071937)
              ·
                refine ⟨1748783353881540159803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331711138508720213071937 1748783353881540159803953)
                ·
                  refine ⟨1311587515411155119852965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748783353881540159803953 1311587515411155119852965)
                  ·
                    refine ⟨245922659139591584972431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311587515411155119852965 245922659139591584972431)
                    ·
                      rfl

theorem cell23_1436798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1436798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436798 prefixEnd_1436798 := by exact prefixLift 1436798
  have htrace : WordTrace (prefixWord ++ tailWord_1436798) baseStart_1436798 baseEnd_1436798 := by
    simpa [prefixWord, tailWord_1436798, baseEnd_1436798] using wordTrace_append hprefix tailTrace_1436798
  have hstable : (prefixWord ++ tailWord_1436798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436798).length < 2 ^ (prefixWord ++ tailWord_1436798).sum := by decide
  have hdescent : baseEnd_1436798 < baseStart_1436798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436803 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 6]
def baseStart_1436803 : Nat := 118140960795 + 1436803 * 2 ^ 59
def prefixEnd_1436803 : Nat := 4983230072969 + 3 ^ 40 * 1436803 * 2
def baseEnd_1436803 : Nat := 245923514940682411784923

theorem tailTrace_1436803 : CollatzResearch.WordTrace tailWord_1436803 prefixEnd_1436803 245923514940682411784923 := by
  unfold tailWord_1436803
  simp only [CollatzResearch.WordTrace]
  refine ⟨52404510613715592261299063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34936340409143728174199375 52404510613715592261299063)
  ·
    refine ⟨78606765920573388391948595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52404510613715592261299063 78606765920573388391948595)
    ·
      refine ⟨117910148880860082587922893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78606765920573388391948595 117910148880860082587922893)
      ·
        refine ⟨44216305830322530970471085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117910148880860082587922893 44216305830322530970471085)
        ·
          refine ⟨16581114686370949113926657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44216305830322530970471085 16581114686370949113926657)
          ·
            refine ⟨12435836014778211835444993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16581114686370949113926657 12435836014778211835444993)
            ·
              refine ⟨9326877011083658876583745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12435836014778211835444993 9326877011083658876583745)
              ·
                refine ⟨6995157758312744157437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326877011083658876583745 6995157758312744157437809)
                ·
                  refine ⟨5246368318734558118078357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995157758312744157437809 5246368318734558118078357)
                  ·
                    refine ⟨245923514940682411784923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5246368318734558118078357 245923514940682411784923)
                    ·
                      rfl

theorem cell23_1436803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_1436803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436803 prefixEnd_1436803 := by exact prefixLift 1436803
  have htrace : WordTrace (prefixWord ++ tailWord_1436803) baseStart_1436803 baseEnd_1436803 := by
    simpa [prefixWord, tailWord_1436803, baseEnd_1436803] using wordTrace_append hprefix tailTrace_1436803
  have hstable : (prefixWord ++ tailWord_1436803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436803).length < 2 ^ (prefixWord ++ tailWord_1436803).sum := by decide
  have hdescent : baseEnd_1436803 < baseStart_1436803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436804 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1436804 : Nat := 118140960795 + 1436804 * 2 ^ 59
def prefixEnd_1436804 : Nat := 4983230072969 + 3 ^ 40 * 1436804 * 2
def baseEnd_1436804 : Nat := 737771058302701731442265

theorem tailTrace_1436804 : CollatzResearch.WordTrace tailWord_1436804 prefixEnd_1436804 737771058302701731442265 := by
  unfold tailWord_1436804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202273543355984716042733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34936364724474646288056977 26202273543355984716042733)
  ·
    refine ⟨9825852578758494268516025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26202273543355984716042733 9825852578758494268516025)
    ·
      refine ⟨7369389434068870701387019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9825852578758494268516025 7369389434068870701387019)
      ·
        refine ⟨11054084151103306052080529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369389434068870701387019 11054084151103306052080529)
        ·
          refine ⟨8290563113327479539060397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11054084151103306052080529 8290563113327479539060397)
          ·
            refine ⟨3108961167497804827147649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8290563113327479539060397 3108961167497804827147649)
            ·
              refine ⟨2331720875623353620360737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108961167497804827147649 2331720875623353620360737)
              ·
                refine ⟨1748790656717515215270553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331720875623353620360737 1748790656717515215270553)
                ·
                  refine ⟨1311592992538136411452915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748790656717515215270553 1311592992538136411452915)
                  ·
                    refine ⟨1967389488807204617179373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311592992538136411452915 1967389488807204617179373)
                    ·
                      refine ⟨737771058302701731442265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967389488807204617179373 737771058302701731442265)
                      ·
                        rfl

theorem cell23_1436804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1436804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436804 prefixEnd_1436804 := by exact prefixLift 1436804
  have htrace : WordTrace (prefixWord ++ tailWord_1436804) baseStart_1436804 baseEnd_1436804 := by
    simpa [prefixWord, tailWord_1436804, baseEnd_1436804] using wordTrace_append hprefix tailTrace_1436804
  have hstable : (prefixWord ++ tailWord_1436804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436804).length < 2 ^ (prefixWord ++ tailWord_1436804).sum := by decide
  have hdescent : baseEnd_1436804 < baseStart_1436804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436805 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_1436805 : Nat := 118140960795 + 1436805 * 2 ^ 59
def prefixEnd_1436805 : Nat := 4983230072969 + 3 ^ 40 * 1436805 * 2
def baseEnd_1436805 : Nat := 737771571783356227529761

theorem tailTrace_1436805 : CollatzResearch.WordTrace tailWord_1436805 prefixEnd_1436805 737771571783356227529761 := by
  unfold tailWord_1436805
  simp only [CollatzResearch.WordTrace]
  refine ⟨52404583559708346602871869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34936389039805564401914579 52404583559708346602871869)
  ·
    refine ⟨19651718834890629976076951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52404583559708346602871869 19651718834890629976076951)
    ·
      refine ⟨29477578252335944964115427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19651718834890629976076951 29477578252335944964115427)
      ·
        refine ⟨44216367378503917446173141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29477578252335944964115427 44216367378503917446173141)
        ·
          refine ⟨1036321110433685565144683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44216367378503917446173141 1036321110433685565144683)
          ·
            refine ⟨1554481665650528347717025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036321110433685565144683 1554481665650528347717025)
            ·
              refine ⟨1165861249237896260787769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554481665650528347717025 1165861249237896260787769)
              ·
                refine ⟨874395936928422195590827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165861249237896260787769 874395936928422195590827)
                ·
                  refine ⟨1311593905392633293386241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874395936928422195590827 1311593905392633293386241)
                  ·
                    refine ⟨983695429044474970039681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311593905392633293386241 983695429044474970039681)
                    ·
                      refine ⟨737771571783356227529761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983695429044474970039681 737771571783356227529761)
                      ·
                        rfl

theorem cell23_1436805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_1436805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436805 prefixEnd_1436805 := by exact prefixLift 1436805
  have htrace : WordTrace (prefixWord ++ tailWord_1436805) baseStart_1436805 baseEnd_1436805 := by
    simpa [prefixWord, tailWord_1436805, baseEnd_1436805] using wordTrace_append hprefix tailTrace_1436805
  have hstable : (prefixWord ++ tailWord_1436805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436805).length < 2 ^ (prefixWord ++ tailWord_1436805).sum := by decide
  have hdescent : baseEnd_1436805 < baseStart_1436805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436873 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_1436873 : Nat := 118140960795 + 1436873 * 2 ^ 59
def prefixEnd_1436873 : Nat := 4983230072969 + 3 ^ 40 * 1436873 * 2
def baseEnd_1436873 : Nat := 737806488467861961479447

theorem tailTrace_1436873 : CollatzResearch.WordTrace tailWord_1436873 prefixEnd_1436873 737806488467861961479447 := by
  unfold tailWord_1436873
  simp only [CollatzResearch.WordTrace]
  refine ⟨52407063723461994216347273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34938042482307996144231515 52407063723461994216347273)
  ·
    refine ⟨39305297792596495662260455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52407063723461994216347273 39305297792596495662260455)
    ·
      refine ⟨58957946688894743493390683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39305297792596495662260455 58957946688894743493390683)
      ·
        refine ⟨88436920033342115240086025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58957946688894743493390683 88436920033342115240086025)
        ·
          refine ⟨66327690025006586430064519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88436920033342115240086025 66327690025006586430064519)
          ·
            refine ⟨99491535037509879645096779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66327690025006586430064519 99491535037509879645096779)
            ·
              refine ⟨149237302556264819467645169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99491535037509879645096779 149237302556264819467645169)
              ·
                refine ⟨111927976917198614600733877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149237302556264819467645169 111927976917198614600733877)
                ·
                  refine ⟨10493247835987370118818801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111927976917198614600733877 10493247835987370118818801)
                  ·
                    refine ⟨7869935876990527589114101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10493247835987370118818801 7869935876990527589114101)
                    ·
                      refine ⟨737806488467861961479447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7869935876990527589114101 737806488467861961479447)
                      ·
                        rfl

theorem cell23_1436873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_1436873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436873 prefixEnd_1436873 := by exact prefixLift 1436873
  have htrace : WordTrace (prefixWord ++ tailWord_1436873) baseStart_1436873 baseEnd_1436873 := by
    simpa [prefixWord, tailWord_1436873, baseEnd_1436873] using wordTrace_append hprefix tailTrace_1436873
  have hstable : (prefixWord ++ tailWord_1436873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436873).length < 2 ^ (prefixWord ++ tailWord_1436873).sum := by decide
  have hdescent : baseEnd_1436873 < baseStart_1436873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436878 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_1436878 : Nat := 118140960795 + 1436878 * 2 ^ 59
def prefixEnd_1436878 : Nat := 4983230072969 + 3 ^ 40 * 1436878 * 2
def baseEnd_1436878 : Nat := 737809055871134441916925

theorem tailTrace_1436878 : CollatzResearch.WordTrace tailWord_1436878 prefixEnd_1436878 737809055871134441916925 := by
  unfold tailWord_1436878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550905761055485008784911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34938164058962586713519525 6550905761055485008784911)
  ·
    refine ⟨9826358641583227513177367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6550905761055485008784911 9826358641583227513177367)
    ·
      refine ⟨14739537962374841269766051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826358641583227513177367 14739537962374841269766051)
      ·
        refine ⟨22109306943562261904649077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739537962374841269766051 22109306943562261904649077)
        ·
          refine ⟨2072747525958962053560851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22109306943562261904649077 2072747525958962053560851)
          ·
            refine ⟨3109121288938443080341277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072747525958962053560851 3109121288938443080341277)
            ·
              refine ⟨1165920483351916155127979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3109121288938443080341277 1165920483351916155127979)
              ·
                refine ⟨1748880725027874232691969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165920483351916155127979 1748880725027874232691969)
                ·
                  refine ⟨1311660543770905674518977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748880725027874232691969 1311660543770905674518977)
                  ·
                    refine ⟨983745407828179255889233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1311660543770905674518977 983745407828179255889233)
                    ·
                      refine ⟨737809055871134441916925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 983745407828179255889233 737809055871134441916925)
                      ·
                        rfl

theorem cell23_1436878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_1436878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436878 prefixEnd_1436878 := by exact prefixLift 1436878
  have htrace : WordTrace (prefixWord ++ tailWord_1436878) baseStart_1436878 baseEnd_1436878 := by
    simpa [prefixWord, tailWord_1436878, baseEnd_1436878] using wordTrace_append hprefix tailTrace_1436878
  have hstable : (prefixWord ++ tailWord_1436878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436878).length < 2 ^ (prefixWord ++ tailWord_1436878).sum := by decide
  have hdescent : baseEnd_1436878 < baseStart_1436878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436900 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1436900 : Nat := 118140960795 + 1436900 * 2 ^ 59
def prefixEnd_1436900 : Nat := 4983230072969 + 3 ^ 40 * 1436900 * 2
def baseEnd_1436900 : Nat := 737820352445533355841823

theorem tailTrace_1436900 : CollatzResearch.WordTrace tailWord_1436900 prefixEnd_1436900 737820352445533355841823 := by
  unfold tailWord_1436900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26204024247182088913790077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34938698996242785218386769 26204024247182088913790077)
  ·
    refine ⟨9826509092693283342671279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26204024247182088913790077 9826509092693283342671279)
    ·
      refine ⟨14739763639039925014006919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826509092693283342671279 14739763639039925014006919)
      ·
        refine ⟨22109645458559887521010379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739763639039925014006919 22109645458559887521010379)
        ·
          refine ⟨33164468187839831281515569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22109645458559887521010379 33164468187839831281515569)
          ·
            refine ⟨24873351140879873461136677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33164468187839831281515569 24873351140879873461136677)
            ·
              refine ⟨4663753338914976273963127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24873351140879873461136677 4663753338914976273963127)
              ·
                refine ⟨6995630008372464410944691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663753338914976273963127 6995630008372464410944691)
                ·
                  refine ⟨10493445012558696616417037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995630008372464410944691 10493445012558696616417037)
                  ·
                    refine ⟨3935041879709511231156389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10493445012558696616417037 3935041879709511231156389)
                    ·
                      refine ⟨737820352445533355841823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3935041879709511231156389 737820352445533355841823)
                      ·
                        rfl

theorem cell23_1436900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1436900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436900 prefixEnd_1436900 := by exact prefixLift 1436900
  have htrace : WordTrace (prefixWord ++ tailWord_1436900) baseStart_1436900 baseEnd_1436900 := by
    simpa [prefixWord, tailWord_1436900, baseEnd_1436900] using wordTrace_append hprefix tailTrace_1436900
  have hstable : (prefixWord ++ tailWord_1436900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436900).length < 2 ^ (prefixWord ++ tailWord_1436900).sum := by decide
  have hdescent : baseEnd_1436900 < baseStart_1436900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436901 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 5]
def baseStart_1436901 : Nat := 118140960795 + 1436901 * 2 ^ 59
def prefixEnd_1436901 : Nat := 4983230072969 + 3 ^ 40 * 1436901 * 2
def baseEnd_1436901 : Nat := 81980096214020872436591

theorem tailTrace_1436901 : CollatzResearch.WordTrace tailWord_1436901 prefixEnd_1436901 81980096214020872436591 := by
  unfold tailWord_1436901
  simp only [CollatzResearch.WordTrace]
  refine ⟨52408084967360554998366557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34938723311573703332244371 52408084967360554998366557)
  ·
    refine ⟨19653031862760208124387459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52408084967360554998366557 19653031862760208124387459)
    ·
      refine ⟨29479547794140312186581189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19653031862760208124387459 29479547794140312186581189)
      ·
        refine ⟨5527415211401308534983973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29479547794140312186581189 5527415211401308534983973)
        ·
          refine ⟨1036390352137745350309495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5527415211401308534983973 1036390352137745350309495)
          ·
            refine ⟨1554585528206618025464243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036390352137745350309495 1554585528206618025464243)
            ·
              refine ⟨2331878292309927038196365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554585528206618025464243 2331878292309927038196365)
              ·
                refine ⟨874454359616222639323637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2331878292309927038196365 874454359616222639323637)
                ·
                  refine ⟨81980096214020872436591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874454359616222639323637 81980096214020872436591)
                  ·
                    rfl

theorem cell23_1436901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_1436901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436901 prefixEnd_1436901 := by exact prefixLift 1436901
  have htrace : WordTrace (prefixWord ++ tailWord_1436901) baseStart_1436901 baseEnd_1436901 := by
    simpa [prefixWord, tailWord_1436901, baseEnd_1436901] using wordTrace_append hprefix tailTrace_1436901
  have hstable : (prefixWord ++ tailWord_1436901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436901).length < 2 ^ (prefixWord ++ tailWord_1436901).sum := by decide
  have hdescent : baseEnd_1436901 < baseStart_1436901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436927 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 3, 4]
def baseStart_1436927 : Nat := 118140960795 + 1436927 * 2 ^ 59
def prefixEnd_1436927 : Nat := 4983230072969 + 3 ^ 40 * 1436927 * 2
def baseEnd_1436927 : Nat := 245944738807734916734733

theorem tailTrace_1436927 : CollatzResearch.WordTrace tailWord_1436927 prefixEnd_1436927 245944738807734916734733 := by
  unfold tailWord_1436927
  simp only [CollatzResearch.WordTrace]
  refine ⟨52409033265266361438813035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34939355510177574292542023 52409033265266361438813035)
  ·
    refine ⟨78613549897899542158219553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52409033265266361438813035 78613549897899542158219553)
    ·
      refine ⟨58960162423424656618664665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78613549897899542158219553 58960162423424656618664665)
      ·
        refine ⟨44220121817568492463998499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58960162423424656618664665 44220121817568492463998499)
        ·
          refine ⟨66330182726352738695997749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44220121817568492463998499 66330182726352738695997749)
          ·
            refine ⟨6218454630595569252749789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66330182726352738695997749 6218454630595569252749789)
            ·
              refine ⟨2331920486473338469781171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6218454630595569252749789 2331920486473338469781171)
              ·
                refine ⟨3497880729710007704671757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331920486473338469781171 3497880729710007704671757)
                ·
                  refine ⟨1311705273641252889251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3497880729710007704671757 1311705273641252889251909)
                  ·
                    refine ⟨245944738807734916734733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311705273641252889251909 245944738807734916734733)
                    ·
                      rfl

theorem cell23_1436927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_1436927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436927 prefixEnd_1436927 := by exact prefixLift 1436927
  have htrace : WordTrace (prefixWord ++ tailWord_1436927) baseStart_1436927 baseEnd_1436927 := by
    simpa [prefixWord, tailWord_1436927, baseEnd_1436927] using wordTrace_append hprefix tailTrace_1436927
  have hstable : (prefixWord ++ tailWord_1436927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436927).length < 2 ^ (prefixWord ++ tailWord_1436927).sum := by decide
  have hdescent : baseEnd_1436927 < baseStart_1436927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436954 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1436954 : Nat := 118140960795 + 1436954 * 2 ^ 59
def prefixEnd_1436954 : Nat := 4983230072969 + 3 ^ 40 * 1436954 * 2
def baseEnd_1436954 : Nat := 737848080400876144566575

theorem tailTrace_1436954 : CollatzResearch.WordTrace tailWord_1436954 prefixEnd_1436954 737848080400876144566575 := by
  unfold tailWord_1436954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102504509042136262511479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34940012024112363366697277 13102504509042136262511479)
  ·
    refine ⟨19653756763563204393767219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13102504509042136262511479 19653756763563204393767219)
    ·
      refine ⟨29480635145344806590650829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19653756763563204393767219 29480635145344806590650829)
      ·
        refine ⟨11055238179504302471494061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29480635145344806590650829 11055238179504302471494061)
        ·
          refine ⟨4145714317314113426810273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11055238179504302471494061 4145714317314113426810273)
          ·
            refine ⟨3109285737985585070107705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145714317314113426810273 3109285737985585070107705)
            ·
              refine ⟨2331964303489188802580779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109285737985585070107705 2331964303489188802580779)
              ·
                refine ⟨3497946455233783203871169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331964303489188802580779 3497946455233783203871169)
                ·
                  refine ⟨2623459841425337402903377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497946455233783203871169 2623459841425337402903377)
                  ·
                    refine ⟨1967594881069003052177533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623459841425337402903377 1967594881069003052177533)
                    ·
                      refine ⟨737848080400876144566575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967594881069003052177533 737848080400876144566575)
                      ·
                        rfl

theorem cell23_1436954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1436954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436954 prefixEnd_1436954 := by exact prefixLift 1436954
  have htrace : WordTrace (prefixWord ++ tailWord_1436954) baseStart_1436954 baseEnd_1436954 := by
    simpa [prefixWord, tailWord_1436954, baseEnd_1436954] using wordTrace_append hprefix tailTrace_1436954
  have hstable : (prefixWord ++ tailWord_1436954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436954).length < 2 ^ (prefixWord ++ tailWord_1436954).sum := by decide
  have hdescent : baseEnd_1436954 < baseStart_1436954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436978 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_1436978 : Nat := 118140960795 + 1436978 * 2 ^ 59
def prefixEnd_1436978 : Nat := 4983230072969 + 3 ^ 40 * 1436978 * 2
def baseEnd_1436978 : Nat := 245953467978861350222155

theorem tailTrace_1436978 : CollatzResearch.WordTrace tailWord_1436978 prefixEnd_1436978 245953467978861350222155 := by
  unfold tailWord_1436978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102723347020399287229897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34940595592054398099279725 13102723347020399287229897)
  ·
    refine ⟨9827042510265299465422423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102723347020399287229897 9827042510265299465422423)
    ·
      refine ⟨14740563765397949198133635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9827042510265299465422423 14740563765397949198133635)
      ·
        refine ⟨22110845648096923797200453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14740563765397949198133635 22110845648096923797200453)
        ·
          refine ⟨4145783559018173211975085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22110845648096923797200453 4145783559018173211975085)
          ·
            refine ⟨1554668834631814954490657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145783559018173211975085 1554668834631814954490657)
            ·
              refine ⟨1166001625973861215867993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554668834631814954490657 1166001625973861215867993)
              ·
                refine ⟨874501219480395911900995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166001625973861215867993 874501219480395911900995)
                ·
                  refine ⟨1311751829220593867851493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874501219480395911900995 1311751829220593867851493)
                  ·
                    refine ⟨245953467978861350222155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311751829220593867851493 245953467978861350222155)
                    ·
                      rfl

theorem cell23_1436978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_1436978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1436978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1436978 prefixEnd_1436978 := by exact prefixLift 1436978
  have htrace : WordTrace (prefixWord ++ tailWord_1436978) baseStart_1436978 baseEnd_1436978 := by
    simpa [prefixWord, tailWord_1436978, baseEnd_1436978] using wordTrace_append hprefix tailTrace_1436978
  have hstable : (prefixWord ++ tailWord_1436978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436978).length < 2 ^ (prefixWord ++ tailWord_1436978).sum := by decide
  have hdescent : baseEnd_1436978 < baseStart_1436978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437005 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1437005 : Nat := 118140960795 + 1437005 * 2 ^ 59
def prefixEnd_1437005 : Nat := 4983230072969 + 3 ^ 40 * 1437005 * 2
def baseEnd_1437005 : Nat := 737874267914255445028841

theorem tailTrace_1437005 : CollatzResearch.WordTrace tailWord_1437005 prefixEnd_1437005 737874267914255445028841 := by
  unfold tailWord_1437005
  simp only [CollatzResearch.WordTrace]
  refine ⟨52411878158983780760152469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34941252105989187173434979 52411878158983780760152469)
  ·
    refine ⟨2456806788702364723132147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52411878158983780760152469 2456806788702364723132147)
    ·
      refine ⟨3685210183053547084698221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456806788702364723132147 3685210183053547084698221)
      ·
        refine ⟨1381953818645080156761833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3685210183053547084698221 1381953818645080156761833)
        ·
          refine ⟨1036465363983810117571375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1381953818645080156761833 1036465363983810117571375)
          ·
            refine ⟨1554698045975715176357063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036465363983810117571375 1554698045975715176357063)
            ·
              refine ⟨2332047068963572764535595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554698045975715176357063 2332047068963572764535595)
              ·
                refine ⟨3498070603445359146803393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332047068963572764535595 3498070603445359146803393)
                ·
                  refine ⟨2623552952584019360102545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3498070603445359146803393 2623552952584019360102545)
                  ·
                    refine ⟨1967664714438014520076909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2623552952584019360102545 1967664714438014520076909)
                    ·
                      refine ⟨737874267914255445028841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967664714438014520076909 737874267914255445028841)
                      ·
                        rfl

theorem cell23_1437005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1437005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437005 prefixEnd_1437005 := by exact prefixLift 1437005
  have htrace : WordTrace (prefixWord ++ tailWord_1437005) baseStart_1437005 baseEnd_1437005 := by
    simpa [prefixWord, tailWord_1437005, baseEnd_1437005] using wordTrace_append hprefix tailTrace_1437005
  have hstable : (prefixWord ++ tailWord_1437005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437005).length < 2 ^ (prefixWord ++ tailWord_1437005).sum := by decide
  have hdescent : baseEnd_1437005 < baseStart_1437005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437024 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1437024 : Nat := 118140960795 + 1437024 * 2 ^ 59
def prefixEnd_1437024 : Nat := 4983230072969 + 3 ^ 40 * 1437024 * 2
def baseEnd_1437024 : Nat := 737884024046690870691253

theorem tailTrace_1437024 : CollatzResearch.WordTrace tailWord_1437024 prefixEnd_1437024 737884024046690870691253 := by
  unfold tailWord_1437024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26206285572957473502547063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34941714097276631336729417 26206285572957473502547063)
  ·
    refine ⟨39309428359436210253820595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26206285572957473502547063 39309428359436210253820595)
    ·
      refine ⟨58964142539154315380730893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39309428359436210253820595 58964142539154315380730893)
      ·
        refine ⟨22111553452182868267774085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58964142539154315380730893 22111553452182868267774085)
        ·
          refine ⟨4145916272284287800207641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22111553452182868267774085 4145916272284287800207641)
          ·
            refine ⟨3109437204213215850155731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145916272284287800207641 3109437204213215850155731)
            ·
              refine ⟨4664155806319823775233597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109437204213215850155731 4664155806319823775233597)
              ·
                refine ⟨1749058427369933915712599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664155806319823775233597 1749058427369933915712599)
                ·
                  refine ⟨2623587641054900873568899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749058427369933915712599 2623587641054900873568899)
                  ·
                    refine ⟨3935381461582351310353349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623587641054900873568899 3935381461582351310353349)
                    ·
                      refine ⟨737884024046690870691253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3935381461582351310353349 737884024046690870691253)
                      ·
                        rfl

theorem cell23_1437024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1437024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437024 prefixEnd_1437024 := by exact prefixLift 1437024
  have htrace : WordTrace (prefixWord ++ tailWord_1437024) baseStart_1437024 baseEnd_1437024 := by
    simpa [prefixWord, tailWord_1437024, baseEnd_1437024] using wordTrace_append hprefix tailTrace_1437024
  have hstable : (prefixWord ++ tailWord_1437024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437024).length < 2 ^ (prefixWord ++ tailWord_1437024).sum := by decide
  have hdescent : baseEnd_1437024 < baseStart_1437024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437050 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1437050 : Nat := 118140960795 + 1437050 * 2 ^ 59
def prefixEnd_1437050 : Nat := 4983230072969 + 3 ^ 40 * 1437050 * 2
def baseEnd_1437050 : Nat := 737897374543707768966133

theorem tailTrace_1437050 : CollatzResearch.WordTrace tailWord_1437050 prefixEnd_1437050 737897374543707768966133 := by
  unfold tailWord_1437050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103379860955188361385151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34942346295880502297027069 13103379860955188361385151)
  ·
    refine ⟨19655069791432782542077727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103379860955188361385151 19655069791432782542077727)
    ·
      refine ⟨29482604687149173813116591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655069791432782542077727 29482604687149173813116591)
      ·
        refine ⟨44223907030723760719674887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29482604687149173813116591 44223907030723760719674887)
        ·
          refine ⟨66335860546085641079512331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44223907030723760719674887 66335860546085641079512331)
          ·
            refine ⟨99503790819128461619268497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66335860546085641079512331 99503790819128461619268497)
            ·
              refine ⟨74627843114346346214451373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99503790819128461619268497 74627843114346346214451373)
              ·
                refine ⟨27985441167879879830419265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74627843114346346214451373 27985441167879879830419265)
                ·
                  refine ⟨20989080875909909872814449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27985441167879879830419265 20989080875909909872814449)
                  ·
                    refine ⟨15741810656932432404610837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20989080875909909872814449 15741810656932432404610837)
                    ·
                      refine ⟨737897374543707768966133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15741810656932432404610837 737897374543707768966133)
                      ·
                        rfl

theorem cell23_1437050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1437050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437050 prefixEnd_1437050 := by exact prefixLift 1437050
  have htrace : WordTrace (prefixWord ++ tailWord_1437050) baseStart_1437050 baseEnd_1437050 := by
    simpa [prefixWord, tailWord_1437050, baseEnd_1437050] using wordTrace_append hprefix tailTrace_1437050
  have hstable : (prefixWord ++ tailWord_1437050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437050).length < 2 ^ (prefixWord ++ tailWord_1437050).sum := by decide
  have hdescent : baseEnd_1437050 < baseStart_1437050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437058 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1437058 : Nat := 118140960795 + 1437058 * 2 ^ 59
def prefixEnd_1437058 : Nat := 4983230072969 + 3 ^ 40 * 1437058 * 2
def baseEnd_1437058 : Nat := 737901482388943737666097

theorem tailTrace_1437058 : CollatzResearch.WordTrace tailWord_1437058 prefixEnd_1437058 737901482388943737666097 := by
  unfold tailWord_1437058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103452806947942702957957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34942540818527847207887885 13103452806947942702957957)
  ·
    refine ⟨2456897401302739256804617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13103452806947942702957957 2456897401302739256804617)
    ·
      refine ⟨1842673050977054442603463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2456897401302739256804617 1842673050977054442603463)
      ·
        refine ⟨2764009576465581663905195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842673050977054442603463 2764009576465581663905195)
        ·
          refine ⟨4146014364698372495857793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764009576465581663905195 4146014364698372495857793)
          ·
            refine ⟨3109510773523779371893345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146014364698372495857793 3109510773523779371893345)
            ·
              refine ⟨2332133080142834528920009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109510773523779371893345 2332133080142834528920009)
              ·
                refine ⟨1749099810107125896690007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332133080142834528920009 1749099810107125896690007)
                ·
                  refine ⟨2623649715160688845035011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749099810107125896690007 2623649715160688845035011)
                  ·
                    refine ⟨3935474572741033267552517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2623649715160688845035011 3935474572741033267552517)
                    ·
                      refine ⟨737901482388943737666097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3935474572741033267552517 737901482388943737666097)
                      ·
                        rfl

theorem cell23_1437058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1437058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437058 prefixEnd_1437058 := by exact prefixLift 1437058
  have htrace : WordTrace (prefixWord ++ tailWord_1437058) baseStart_1437058 baseEnd_1437058 := by
    simpa [prefixWord, tailWord_1437058, baseEnd_1437058] using wordTrace_append hprefix tailTrace_1437058
  have hstable : (prefixWord ++ tailWord_1437058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437058).length < 2 ^ (prefixWord ++ tailWord_1437058).sum := by decide
  have hdescent : baseEnd_1437058 < baseStart_1437058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437064 : List Nat := [2, 1, 3, 3, 1, 4, 2, 7]
def baseStart_1437064 : Nat := 118140960795 + 1437064 * 2 ^ 59
def prefixEnd_1437064 : Nat := 4983230072969 + 3 ^ 40 * 1437064 * 2
def baseEnd_1437064 : Nat := 27329798639735952377447

theorem tailTrace_1437064 : CollatzResearch.WordTrace tailWord_1437064 prefixEnd_1437064 27329798639735952377447 := by
  unfold tailWord_1437064
  simp only [CollatzResearch.WordTrace]
  refine ⟨26207015032885016918275123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34942686710513355891033497 26207015032885016918275123)
  ·
    refine ⟨39310522549327525377412685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26207015032885016918275123 39310522549327525377412685)
    ·
      refine ⟨14741445955997822016529757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39310522549327525377412685 14741445955997822016529757)
      ·
        refine ⟨5528042233499183256198659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14741445955997822016529757 5528042233499183256198659)
        ·
          refine ⟨8292063350248774884297989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528042233499183256198659 8292063350248774884297989)
          ·
            refine ⟨1554761878171645290805873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8292063350248774884297989 1554761878171645290805873)
            ·
              refine ⟨1166071408628733968104405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554761878171645290805873 1166071408628733968104405)
              ·
                refine ⟨27329798639735952377447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1166071408628733968104405 27329798639735952377447)
                ·
                  rfl

theorem cell23_1437064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 7].length) (baseStart_1437064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437064 prefixEnd_1437064 := by exact prefixLift 1437064
  have htrace : WordTrace (prefixWord ++ tailWord_1437064) baseStart_1437064 baseEnd_1437064 := by
    simpa [prefixWord, tailWord_1437064, baseEnd_1437064] using wordTrace_append hprefix tailTrace_1437064
  have hstable : (prefixWord ++ tailWord_1437064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437064).length < 2 ^ (prefixWord ++ tailWord_1437064).sum := by decide
  have hdescent : baseEnd_1437064 < baseStart_1437064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437117 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1437117 : Nat := 118140960795 + 1437117 * 2 ^ 59
def prefixEnd_1437117 : Nat := 4983230072969 + 3 ^ 40 * 1437117 * 2
def baseEnd_1437117 : Nat := 737931777747559006828325

theorem tailTrace_1437117 : CollatzResearch.WordTrace tailWord_1437117 prefixEnd_1437117 737931777747559006828325 := by
  unfold tailWord_1437117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52415963134578023888229605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34943975423052015925486403 52415963134578023888229605)
  ·
    refine ⟨9827993087733379479043051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52415963134578023888229605 9827993087733379479043051)
    ·
      refine ⟨14741989631600069218564577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9827993087733379479043051 14741989631600069218564577)
      ·
        refine ⟨11056492223700051913923433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14741989631600069218564577 11056492223700051913923433)
        ·
          refine ⟨8292369167775038935442575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056492223700051913923433 8292369167775038935442575)
          ·
            refine ⟨12438553751662558403163863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292369167775038935442575 12438553751662558403163863)
            ·
              refine ⟨18657830627493837604745795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12438553751662558403163863 18657830627493837604745795)
              ·
                refine ⟨27986745941240756407118693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18657830627493837604745795 27986745941240756407118693)
                ·
                  refine ⟨5247514863982641826334755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27986745941240756407118693 5247514863982641826334755)
                  ·
                    refine ⟨7871272295973962739502133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247514863982641826334755 7871272295973962739502133)
                    ·
                      refine ⟨737931777747559006828325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7871272295973962739502133 737931777747559006828325)
                      ·
                        rfl

theorem cell23_1437117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1437117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437117 prefixEnd_1437117 := by exact prefixLift 1437117
  have htrace : WordTrace (prefixWord ++ tailWord_1437117) baseStart_1437117 baseEnd_1437117 := by
    simpa [prefixWord, tailWord_1437117, baseEnd_1437117] using wordTrace_append hprefix tailTrace_1437117
  have hstable : (prefixWord ++ tailWord_1437117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437117).length < 2 ^ (prefixWord ++ tailWord_1437117).sum := by decide
  have hdescent : baseEnd_1437117 < baseStart_1437117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437147 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3]
def baseStart_1437147 : Nat := 118140960795 + 1437147 * 2 ^ 59
def prefixEnd_1437147 : Nat := 4983230072969 + 3 ^ 40 * 1437147 * 2
def baseEnd_1437147 : Nat := 737947182167193889453187

theorem tailTrace_1437147 : CollatzResearch.WordTrace tailWord_1437147 prefixEnd_1437147 737947182167193889453187 := by
  unfold tailWord_1437147
  simp only [CollatzResearch.WordTrace]
  refine ⟨52417057324469339011821695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34944704882979559341214463 52417057324469339011821695)
  ·
    refine ⟨78625585986704008517732543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52417057324469339011821695 78625585986704008517732543)
    ·
      refine ⟨117938378980056012776598815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78625585986704008517732543 117938378980056012776598815)
      ·
        refine ⟨176907568470084019164898223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117938378980056012776598815 176907568470084019164898223)
        ·
          refine ⟨265361352705126028747347335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176907568470084019164898223 265361352705126028747347335)
          ·
            refine ⟨398042029057689043121021003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265361352705126028747347335 398042029057689043121021003)
            ·
              refine ⟨597063043586533564681531505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398042029057689043121021003 597063043586533564681531505)
              ·
                refine ⟨447797282689900173511148629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597063043586533564681531505 447797282689900173511148629)
                ·
                  refine ⟨5247624406522267658333773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 447797282689900173511148629 5247624406522267658333773)
                  ·
                    refine ⟨1967859152445850371875165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5247624406522267658333773 1967859152445850371875165)
                    ·
                      refine ⟨737947182167193889453187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1967859152445850371875165 737947182167193889453187)
                      ·
                        rfl

theorem cell23_1437147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].length) (baseStart_1437147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437147 prefixEnd_1437147 := by exact prefixLift 1437147
  have htrace : WordTrace (prefixWord ++ tailWord_1437147) baseStart_1437147 baseEnd_1437147 := by
    simpa [prefixWord, tailWord_1437147, baseEnd_1437147] using wordTrace_append hprefix tailTrace_1437147
  have hstable : (prefixWord ++ tailWord_1437147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437147).length < 2 ^ (prefixWord ++ tailWord_1437147).sum := by decide
  have hdescent : baseEnd_1437147 < baseStart_1437147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437167 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 4, 5]
def baseStart_1437167 : Nat := 118140960795 + 1437167 * 2 ^ 59
def prefixEnd_1437167 : Nat := 4983230072969 + 3 ^ 40 * 1437167 * 2
def baseEnd_1437167 : Nat := 245985817260094603734365

theorem tailTrace_1437167 : CollatzResearch.WordTrace tailWord_1437167 prefixEnd_1437167 245985817260094603734365 := by
  unfold tailWord_1437167
  simp only [CollatzResearch.WordTrace]
  refine ⟨52417786784396882427549755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34945191189597921618366503 52417786784396882427549755)
  ·
    refine ⟨78626680176595323641324633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52417786784396882427549755 78626680176595323641324633)
    ·
      refine ⟨58970010132446492730993475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78626680176595323641324633 58970010132446492730993475)
      ·
        refine ⟨88455015198669739096490213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58970010132446492730993475 88455015198669739096490213)
        ·
          refine ⟨16585315349750576080591915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88455015198669739096490213 16585315349750576080591915)
          ·
            refine ⟨24877973024625864120887873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16585315349750576080591915 24877973024625864120887873)
            ·
              refine ⟨18658479768469398090665905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24877973024625864120887873 18658479768469398090665905)
              ·
                refine ⟨13993859826352048567999429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18658479768469398090665905 13993859826352048567999429)
                ·
                  refine ⟨2623848717441009106499893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13993859826352048567999429 2623848717441009106499893)
                  ·
                    refine ⟨245985817260094603734365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2623848717441009106499893 245985817260094603734365)
                    ·
                      rfl

theorem cell23_1437167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_1437167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437167 prefixEnd_1437167 := by exact prefixLift 1437167
  have htrace : WordTrace (prefixWord ++ tailWord_1437167) baseStart_1437167 baseEnd_1437167 := by
    simpa [prefixWord, tailWord_1437167, baseEnd_1437167] using wordTrace_append hprefix tailTrace_1437167
  have hstable : (prefixWord ++ tailWord_1437167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437167).length < 2 ^ (prefixWord ++ tailWord_1437167).sum := by decide
  have hdescent : baseEnd_1437167 < baseStart_1437167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437188 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1437188 : Nat := 118140960795 + 1437188 * 2 ^ 59
def prefixEnd_1437188 : Nat := 4983230072969 + 3 ^ 40 * 1437188 * 2
def baseEnd_1437188 : Nat := 81996470541558692115611

theorem tailTrace_1437188 : CollatzResearch.WordTrace tailWord_1437188 prefixEnd_1437188 81996470541558692115611 := by
  unfold tailWord_1437188
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209276358660401507032109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34945701811547202009376145 26209276358660401507032109)
  ·
    refine ⟨9828478634497650565137041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26209276358660401507032109 9828478634497650565137041)
    ·
      refine ⟨7371358975873237923852781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9828478634497650565137041 7371358975873237923852781)
      ·
        refine ⟨2764259615952464221444793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7371358975873237923852781 2764259615952464221444793)
        ·
          refine ⟨2073194711964348166083595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764259615952464221444793 2073194711964348166083595)
          ·
            refine ⟨3109792067946522249125393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073194711964348166083595 3109792067946522249125393)
            ·
              refine ⟨2332344050959891686844045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109792067946522249125393 2332344050959891686844045)
              ·
                refine ⟨874629019109959382566517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332344050959891686844045 874629019109959382566517)
                ·
                  refine ⟨81996470541558692115611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874629019109959382566517 81996470541558692115611)
                  ·
                    rfl

theorem cell23_1437188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1437188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437188 prefixEnd_1437188 := by exact prefixLift 1437188
  have htrace : WordTrace (prefixWord ++ tailWord_1437188) baseStart_1437188 baseEnd_1437188 := by
    simpa [prefixWord, tailWord_1437188, baseEnd_1437188] using wordTrace_append hprefix tailTrace_1437188
  have hstable : (prefixWord ++ tailWord_1437188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437188).length < 2 ^ (prefixWord ++ tailWord_1437188).sum := by decide
  have hdescent : baseEnd_1437188 < baseStart_1437188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437267 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_1437267 : Nat := 118140960795 + 1437267 * 2 ^ 59
def prefixEnd_1437267 : Nat := 4983230072969 + 3 ^ 40 * 1437267 * 2
def baseEnd_1437267 : Nat := 738008799845733419952635

theorem tailTrace_1437267 : CollatzResearch.WordTrace tailWord_1437267 prefixEnd_1437267 738008799845733419952635 := by
  unfold tailWord_1437267
  simp only [CollatzResearch.WordTrace]
  refine ⟨52421434084034599506190055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34947622722689733004126703 52421434084034599506190055)
  ·
    refine ⟨78632151126051899259285083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52421434084034599506190055 78632151126051899259285083)
    ·
      refine ⟨117948226689077848888927625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78632151126051899259285083 117948226689077848888927625)
      ·
        refine ⟨88461170016808386666695719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117948226689077848888927625 88461170016808386666695719)
        ·
          refine ⟨132691755025212580000043579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88461170016808386666695719 132691755025212580000043579)
          ·
            refine ⟨199037632537818870000065369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132691755025212580000043579 199037632537818870000065369)
            ·
              refine ⟨149278224403364152500049027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199037632537818870000065369 149278224403364152500049027)
              ·
                refine ⟨223917336605046228750073541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149278224403364152500049027 223917336605046228750073541)
                ·
                  refine ⟨41984500613446167890638789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223917336605046228750073541 41984500613446167890638789)
                  ·
                    refine ⟨7872093865021156479494773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41984500613446167890638789 7872093865021156479494773)
                    ·
                      refine ⟨738008799845733419952635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7872093865021156479494773 738008799845733419952635)
                      ·
                        rfl

theorem cell23_1437267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_1437267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437267 prefixEnd_1437267 := by exact prefixLift 1437267
  have htrace : WordTrace (prefixWord ++ tailWord_1437267) baseStart_1437267 baseEnd_1437267 := by
    simpa [prefixWord, tailWord_1437267, baseEnd_1437267] using wordTrace_append hprefix tailTrace_1437267
  have hstable : (prefixWord ++ tailWord_1437267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437267).length < 2 ^ (prefixWord ++ tailWord_1437267).sum := by decide
  have hdescent : baseEnd_1437267 < baseStart_1437267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437281 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_1437281 : Nat := 118140960795 + 1437281 * 2 ^ 59
def prefixEnd_1437281 : Nat := 4983230072969 + 3 ^ 40 * 1437281 * 2
def baseEnd_1437281 : Nat := 738015988574896365177571

theorem tailTrace_1437281 : CollatzResearch.WordTrace tailWord_1437281 prefixEnd_1437281 738015988574896365177571 := by
  unfold tailWord_1437281
  simp only [CollatzResearch.WordTrace]
  refine ⟨52421944705983879897199697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34947963137322586598133131 52421944705983879897199697)
  ·
    refine ⟨39316458529487909922899773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52421944705983879897199697 39316458529487909922899773)
    ·
      refine ⟨14743671948557966221087415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39316458529487909922899773 14743671948557966221087415)
      ·
        refine ⟨22115507922836949331631123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743671948557966221087415 22115507922836949331631123)
        ·
          refine ⟨33173261884255423997446685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22115507922836949331631123 33173261884255423997446685)
          ·
            refine ⟨12439973206595783999042507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33173261884255423997446685 12439973206595783999042507)
            ·
              refine ⟨18659959809893675998563761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439973206595783999042507 18659959809893675998563761)
              ·
                refine ⟨13994969857420256998922821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18659959809893675998563761 13994969857420256998922821)
                ·
                  refine ⟨2624056848266298187298029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13994969857420256998922821 2624056848266298187298029)
                  ·
                    refine ⟨984021318099861820236761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624056848266298187298029 984021318099861820236761)
                    ·
                      refine ⟨738015988574896365177571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984021318099861820236761 738015988574896365177571)
                      ·
                        rfl

theorem cell23_1437281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_1437281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437281 prefixEnd_1437281 := by exact prefixLift 1437281
  have htrace : WordTrace (prefixWord ++ tailWord_1437281) baseStart_1437281 baseEnd_1437281 := by
    simpa [prefixWord, tailWord_1437281, baseEnd_1437281] using wordTrace_append hprefix tailTrace_1437281
  have hstable : (prefixWord ++ tailWord_1437281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437281).length < 2 ^ (prefixWord ++ tailWord_1437281).sum := by decide
  have hdescent : baseEnd_1437281 < baseStart_1437281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437298 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1437298 : Nat := 118140960795 + 1437298 * 2 ^ 59
def prefixEnd_1437298 : Nat := 4983230072969 + 3 ^ 40 * 1437298 * 2
def baseEnd_1437298 : Nat := 738024717746022798664993

theorem tailTrace_1437298 : CollatzResearch.WordTrace tailWord_1437298 prefixEnd_1437298 738024717746022798664993 := by
  unfold tailWord_1437298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105641186730572950142137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34948376497948194533712365 13105641186730572950142137)
  ·
    refine ⟨9829230890047929712606603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13105641186730572950142137 9829230890047929712606603)
    ·
      refine ⟨14743846335071894568909905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9829230890047929712606603 14743846335071894568909905)
      ·
        refine ⟨11057884751303920926682429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14743846335071894568909905 11057884751303920926682429)
        ·
          refine ⟨4146706781738970347505911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11057884751303920926682429 4146706781738970347505911)
          ·
            refine ⟨6220060172608455521258867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146706781738970347505911 6220060172608455521258867)
            ·
              refine ⟨9330090258912683281888301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220060172608455521258867 9330090258912683281888301)
              ·
                refine ⟨3498783847092256230708113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9330090258912683281888301 3498783847092256230708113)
                ·
                  refine ⟨2624087885319192173031085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3498783847092256230708113 2624087885319192173031085)
                  ·
                    refine ⟨984032956994697064886657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624087885319192173031085 984032956994697064886657)
                    ·
                      refine ⟨738024717746022798664993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984032956994697064886657 738024717746022798664993)
                      ·
                        rfl

theorem cell23_1437298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1437298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437298 prefixEnd_1437298 := by exact prefixLift 1437298
  have htrace : WordTrace (prefixWord ++ tailWord_1437298) baseStart_1437298 baseEnd_1437298 := by
    simpa [prefixWord, tailWord_1437298, baseEnd_1437298] using wordTrace_append hprefix tailTrace_1437298
  have hstable : (prefixWord ++ tailWord_1437298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437298).length < 2 ^ (prefixWord ++ tailWord_1437298).sum := by decide
  have hdescent : baseEnd_1437298 < baseStart_1437298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437321 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_1437321 : Nat := 118140960795 + 1437321 * 2 ^ 59
def prefixEnd_1437321 : Nat := 4983230072969 + 3 ^ 40 * 1437321 * 2
def baseEnd_1437321 : Nat := 246012175933692069559129

theorem tailTrace_1437321 : CollatzResearch.WordTrace tailWord_1437321 prefixEnd_1437321 246012175933692069559129 := by
  unfold tailWord_1437321
  simp only [CollatzResearch.WordTrace]
  refine ⟨52423403625838966728655817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34948935750559311152437211 52423403625838966728655817)
  ·
    refine ⟨39317552719379225046491863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52423403625838966728655817 39317552719379225046491863)
    ·
      refine ⟨58976329079068837569737795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39317552719379225046491863 58976329079068837569737795)
      ·
        refine ⟨88464493618603256354606693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58976329079068837569737795 88464493618603256354606693)
        ·
          refine ⟨16587092553488110566488755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88464493618603256354606693 16587092553488110566488755)
          ·
            refine ⟨24880638830232165849733133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16587092553488110566488755 24880638830232165849733133)
            ·
              refine ⟨9330239561337062193649925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24880638830232165849733133 9330239561337062193649925)
              ·
                refine ⟨1749419917750699161309361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9330239561337062193649925 1749419917750699161309361)
                ·
                  refine ⟨1312064938313024370982021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1749419917750699161309361 1312064938313024370982021)
                  ·
                    refine ⟨246012175933692069559129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312064938313024370982021 246012175933692069559129)
                    ·
                      rfl

theorem cell23_1437321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_1437321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437321 prefixEnd_1437321 := by exact prefixLift 1437321
  have htrace : WordTrace (prefixWord ++ tailWord_1437321) baseStart_1437321 baseEnd_1437321 := by
    simpa [prefixWord, tailWord_1437321, baseEnd_1437321] using wordTrace_append hprefix tailTrace_1437321
  have hstable : (prefixWord ++ tailWord_1437321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437321).length < 2 ^ (prefixWord ++ tailWord_1437321).sum := by decide
  have hdescent : baseEnd_1437321 < baseStart_1437321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437322 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_1437322 : Nat := 118140960795 + 1437322 * 2 ^ 59
def prefixEnd_1437322 : Nat := 4983230072969 + 3 ^ 40 * 1437322 * 2
def baseEnd_1437322 : Nat := 738037041281730704764883

theorem tailTrace_1437322 : CollatzResearch.WordTrace tailWord_1437322 prefixEnd_1437322 738037041281730704764883 := by
  unfold tailWord_1437322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105860024708835974860555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34948960065890229266294813 13105860024708835974860555)
  ·
    refine ⟨19658790037063253962290833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13105860024708835974860555 19658790037063253962290833)
    ·
      refine ⟨14744092527797440471718125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19658790037063253962290833 14744092527797440471718125)
      ·
        refine ⟨5529034697924040176894297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14744092527797440471718125 5529034697924040176894297)
        ·
          refine ⟨4146776023443030132670723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529034697924040176894297 4146776023443030132670723)
          ·
            refine ⟨6220164035164545199006085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146776023443030132670723 6220164035164545199006085)
            ·
              refine ⟨1166280756593352224813641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6220164035164545199006085 1166280756593352224813641)
              ·
                refine ⟨874710567445014168610231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166280756593352224813641 874710567445014168610231)
                ·
                  refine ⟨1312065851167521252915347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874710567445014168610231 1312065851167521252915347)
                  ·
                    refine ⟨1968098776751281879373021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312065851167521252915347 1968098776751281879373021)
                    ·
                      refine ⟨738037041281730704764883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968098776751281879373021 738037041281730704764883)
                      ·
                        rfl

theorem cell23_1437322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_1437322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437322 prefixEnd_1437322 := by exact prefixLift 1437322
  have htrace : WordTrace (prefixWord ++ tailWord_1437322) baseStart_1437322 baseEnd_1437322 := by
    simpa [prefixWord, tailWord_1437322, baseEnd_1437322] using wordTrace_append hprefix tailTrace_1437322
  have hstable : (prefixWord ++ tailWord_1437322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437322).length < 2 ^ (prefixWord ++ tailWord_1437322).sum := by decide
  have hdescent : baseEnd_1437322 < baseStart_1437322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437324 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1437324 : Nat := 118140960795 + 1437324 * 2 ^ 59
def prefixEnd_1437324 : Nat := 4983230072969 + 3 ^ 40 * 1437324 * 2
def baseEnd_1437324 : Nat := 738038068243039696939873

theorem tailTrace_1437324 : CollatzResearch.WordTrace tailWord_1437324 prefixEnd_1437324 738038068243039696939873 := by
  unfold tailWord_1437324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211756522414049120507513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34949008696552065494010017 26211756522414049120507513)
  ·
    refine ⟨19658817391810536840380635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26211756522414049120507513 19658817391810536840380635)
    ·
      refine ⟨29488226087715805260570953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658817391810536840380635 29488226087715805260570953)
      ·
        refine ⟨22116169565786853945428215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29488226087715805260570953 22116169565786853945428215)
        ·
          refine ⟨33174254348680280918142323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22116169565786853945428215 33174254348680280918142323)
          ·
            refine ⟨49761381523020421377213485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33174254348680280918142323 49761381523020421377213485)
            ·
              refine ⟨18660518071132658016455057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49761381523020421377213485 18660518071132658016455057)
              ·
                refine ⟨13995388553349493512341293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18660518071132658016455057 13995388553349493512341293)
                ·
                  refine ⟨5248270707506060067127985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13995388553349493512341293 5248270707506060067127985)
                  ·
                    refine ⟨3936203030629545050345989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5248270707506060067127985 3936203030629545050345989)
                    ·
                      refine ⟨738038068243039696939873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3936203030629545050345989 738038068243039696939873)
                      ·
                        rfl

theorem cell23_1437324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1437324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437324 prefixEnd_1437324 := by exact prefixLift 1437324
  have htrace : WordTrace (prefixWord ++ tailWord_1437324) baseStart_1437324 baseEnd_1437324 := by
    simpa [prefixWord, tailWord_1437324, baseEnd_1437324] using wordTrace_append hprefix tailTrace_1437324
  have hstable : (prefixWord ++ tailWord_1437324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437324).length < 2 ^ (prefixWord ++ tailWord_1437324).sum := by decide
  have hdescent : baseEnd_1437324 < baseStart_1437324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437345 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1437345 : Nat := 118140960795 + 1437345 * 2 ^ 59
def prefixEnd_1437345 : Nat := 4983230072969 + 3 ^ 40 * 1437345 * 2
def baseEnd_1437345 : Nat := 738048851336784114777277

theorem tailTrace_1437345 : CollatzResearch.WordTrace tailWord_1437345 prefixEnd_1437345 738048851336784114777277 := by
  unfold tailWord_1437345
  simp only [CollatzResearch.WordTrace]
  refine ⟨52424278977752018827529489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34949519318501345885019659 52424278977752018827529489)
  ·
    refine ⟨39318209233314014120647117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52424278977752018827529489 39318209233314014120647117)
    ·
      refine ⟨14744328462492755295242669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39318209233314014120647117 14744328462492755295242669)
      ·
        refine ⟨5529123173434783235716001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14744328462492755295242669 5529123173434783235716001)
        ·
          refine ⟨4146842380076087426787001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529123173434783235716001 4146842380076087426787001)
          ·
            refine ⟨3110131785057065570090251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146842380076087426787001 3110131785057065570090251)
            ·
              refine ⟨4665197677585598355135377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110131785057065570090251 4665197677585598355135377)
              ·
                refine ⟨3498898258189198766351533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4665197677585598355135377 3498898258189198766351533)
                ·
                  refine ⟨1312086846820949537381825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3498898258189198766351533 1312086846820949537381825)
                  ·
                    refine ⟨984065135115712153036369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312086846820949537381825 984065135115712153036369)
                    ·
                      refine ⟨738048851336784114777277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984065135115712153036369 738048851336784114777277)
                      ·
                        rfl

theorem cell23_1437345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1437345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437345 prefixEnd_1437345 := by exact prefixLift 1437345
  have htrace : WordTrace (prefixWord ++ tailWord_1437345) baseStart_1437345 baseEnd_1437345 := by
    simpa [prefixWord, tailWord_1437345, baseEnd_1437345] using wordTrace_append hprefix tailTrace_1437345
  have hstable : (prefixWord ++ tailWord_1437345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437345).length < 2 ^ (prefixWord ++ tailWord_1437345).sum := by decide
  have hdescent : baseEnd_1437345 < baseStart_1437345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437365 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1437365 : Nat := 118140960795 + 1437365 * 2 ^ 59
def prefixEnd_1437365 : Nat := 4983230072969 + 3 ^ 40 * 1437365 * 2
def baseEnd_1437365 : Nat := 738059120949874036527185

theorem tailTrace_1437365 : CollatzResearch.WordTrace tailWord_1437365 prefixEnd_1437365 738059120949874036527185 := by
  unfold tailWord_1437365
  simp only [CollatzResearch.WordTrace]
  refine ⟨52425008437679562243257549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34950005625119708162171699 52425008437679562243257549)
  ·
    refine ⟨19659378164129835841221581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52425008437679562243257549 19659378164129835841221581)
    ·
      refine ⟨7372266811548688440458093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19659378164129835841221581 7372266811548688440458093)
      ·
        refine ⟨2764600054330758165171785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7372266811548688440458093 2764600054330758165171785)
        ·
          refine ⟨2073450040748068623878839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764600054330758165171785 2073450040748068623878839)
          ·
            refine ⟨3110175061122102935818259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073450040748068623878839 3110175061122102935818259)
            ·
              refine ⟨4665262591683154403727389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110175061122102935818259 4665262591683154403727389)
              ·
                refine ⟨1749473471881182901397771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665262591683154403727389 1749473471881182901397771)
                ·
                  refine ⟨2624210207821774352096657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749473471881182901397771 2624210207821774352096657)
                  ·
                    refine ⟨1968157655866330764072493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624210207821774352096657 1968157655866330764072493)
                    ·
                      refine ⟨738059120949874036527185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968157655866330764072493 738059120949874036527185)
                      ·
                        rfl

theorem cell23_1437365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1437365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437365 prefixEnd_1437365 := by exact prefixLift 1437365
  have htrace : WordTrace (prefixWord ++ tailWord_1437365) baseStart_1437365 baseEnd_1437365 := by
    simpa [prefixWord, tailWord_1437365, baseEnd_1437365] using wordTrace_append hprefix tailTrace_1437365
  have hstable : (prefixWord ++ tailWord_1437365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437365).length < 2 ^ (prefixWord ++ tailWord_1437365).sum := by decide
  have hdescent : baseEnd_1437365 < baseStart_1437365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437418 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_1437418 : Nat := 118140960795 + 1437418 * 2 ^ 59
def prefixEnd_1437418 : Nat := 4983230072969 + 3 ^ 40 * 1437418 * 2
def baseEnd_1437418 : Nat := 738086335424562329164441

theorem tailTrace_1437418 : CollatzResearch.WordTrace tailWord_1437418 prefixEnd_1437418 738086335424562329164441 := by
  unfold tailWord_1437418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13106735376621888073734227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34951294337658368196624605 13106735376621888073734227)
  ·
    refine ⟨19660103064932832110601341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13106735376621888073734227 19660103064932832110601341)
    ·
      refine ⟨7372538649349812041475503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19660103064932832110601341 7372538649349812041475503)
      ·
        refine ⟨11058807974024718062213255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372538649349812041475503 11058807974024718062213255)
        ·
          refine ⟨16588211961037077093319883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058807974024718062213255 16588211961037077093319883)
          ·
            refine ⟨24882317941555615639979825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588211961037077093319883 24882317941555615639979825)
            ·
              refine ⟨18661738456166711729984869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24882317941555615639979825 18661738456166711729984869)
              ·
                refine ⟨3499075960531258449372163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18661738456166711729984869 3499075960531258449372163)
                ·
                  refine ⟨5248613940796887674058245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499075960531258449372163 5248613940796887674058245)
                  ·
                    refine ⟨984115113899416438885921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248613940796887674058245 984115113899416438885921)
                    ·
                      refine ⟨738086335424562329164441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984115113899416438885921 738086335424562329164441)
                      ·
                        rfl

theorem cell23_1437418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_1437418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437418 prefixEnd_1437418 := by exact prefixLift 1437418
  have htrace : WordTrace (prefixWord ++ tailWord_1437418) baseStart_1437418 baseEnd_1437418 := by
    simpa [prefixWord, tailWord_1437418, baseEnd_1437418] using wordTrace_append hprefix tailTrace_1437418
  have hstable : (prefixWord ++ tailWord_1437418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437418).length < 2 ^ (prefixWord ++ tailWord_1437418).sum := by decide
  have hdescent : baseEnd_1437418 < baseStart_1437418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437421 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1437421 : Nat := 118140960795 + 1437421 * 2 ^ 59
def prefixEnd_1437421 : Nat := 4983230072969 + 3 ^ 40 * 1437421 * 2
def baseEnd_1437421 : Nat := 738087875866525817426927

theorem tailTrace_1437421 : CollatzResearch.WordTrace tailWord_1437421 prefixEnd_1437421 738087875866525817426927 := by
  unfold tailWord_1437421
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427050925476683807296117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34951367283651122538197411 52427050925476683807296117)
  ·
    refine ⟨4915036024263439106934011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52427050925476683807296117 4915036024263439106934011)
    ·
      refine ⟨7372554036395158660401017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915036024263439106934011 7372554036395158660401017)
      ·
        refine ⟨5529415527296368995300763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7372554036395158660401017 5529415527296368995300763)
        ·
          refine ⟨8294123290944553492951145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529415527296368995300763 8294123290944553492951145)
          ·
            refine ⟨6220592468208415119713359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294123290944553492951145 6220592468208415119713359)
            ·
              refine ⟨9330888702312622679570039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220592468208415119713359 9330888702312622679570039)
              ·
                refine ⟨13996333053468934019355059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330888702312622679570039 13996333053468934019355059)
                ·
                  refine ⟨20994499580203401029032589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13996333053468934019355059 20994499580203401029032589)
                  ·
                    refine ⟨7872937342576275385887221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20994499580203401029032589 7872937342576275385887221)
                    ·
                      refine ⟨738087875866525817426927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7872937342576275385887221 738087875866525817426927)
                      ·
                        rfl

theorem cell23_1437421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1437421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437421 prefixEnd_1437421 := by exact prefixLift 1437421
  have htrace : WordTrace (prefixWord ++ tailWord_1437421) baseStart_1437421 baseEnd_1437421 := by
    simpa [prefixWord, tailWord_1437421, baseEnd_1437421] using wordTrace_append hprefix tailTrace_1437421
  have hstable : (prefixWord ++ tailWord_1437421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437421).length < 2 ^ (prefixWord ++ tailWord_1437421).sum := by decide
  have hdescent : baseEnd_1437421 < baseStart_1437421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437434 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1437434 : Nat := 118140960795 + 1437434 * 2 ^ 59
def prefixEnd_1437434 : Nat := 4983230072969 + 3 ^ 40 * 1437434 * 2
def baseEnd_1437434 : Nat := 738094551115034266564367

theorem tailTrace_1437434 : CollatzResearch.WordTrace tailWord_1437434 prefixEnd_1437434 738094551115034266564367 := by
  unfold tailWord_1437434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13106881268607396756879839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34951683382953058018346237 13106881268607396756879839)
  ·
    refine ⟨19660321902911095135319759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13106881268607396756879839 19660321902911095135319759)
    ·
      refine ⟨29490482854366642702979639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19660321902911095135319759 29490482854366642702979639)
      ·
        refine ⟨44235724281549964054469459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29490482854366642702979639 44235724281549964054469459)
        ·
          refine ⟨66353586422324946081704189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44235724281549964054469459 66353586422324946081704189)
          ·
            refine ⟨24882594908371854780639071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66353586422324946081704189 24882594908371854780639071)
            ·
              refine ⟨37323892362557782170958607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24882594908371854780639071 37323892362557782170958607)
              ·
                refine ⟨55985838543836673256437911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37323892362557782170958607 55985838543836673256437911)
                ·
                  refine ⟨83978757815755009884656867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55985838543836673256437911 83978757815755009884656867)
                  ·
                    refine ⟨125968136723632514826985301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83978757815755009884656867 125968136723632514826985301)
                    ·
                      refine ⟨738094551115034266564367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 125968136723632514826985301 738094551115034266564367)
                      ·
                        rfl

theorem cell23_1437434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1437434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437434 prefixEnd_1437434 := by exact prefixLift 1437434
  have htrace : WordTrace (prefixWord ++ tailWord_1437434) baseStart_1437434 baseEnd_1437434 := by
    simpa [prefixWord, tailWord_1437434, baseEnd_1437434] using wordTrace_append hprefix tailTrace_1437434
  have hstable : (prefixWord ++ tailWord_1437434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437434).length < 2 ^ (prefixWord ++ tailWord_1437434).sum := by decide
  have hdescent : baseEnd_1437434 < baseStart_1437434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437441 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 7]
def baseStart_1437441 : Nat := 118140960795 + 1437441 * 2 ^ 59
def prefixEnd_1437441 : Nat := 4983230072969 + 3 ^ 40 * 1437441 * 2
def baseEnd_1437441 : Nat := 82010905053290637686315

theorem tailTrace_1437441 : CollatzResearch.WordTrace tailWord_1437441 prefixEnd_1437441 82010905053290637686315 := by
  unfold tailWord_1437441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427780385404227223024177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34951853590269484815349451 52427780385404227223024177)
  ·
    refine ⟨39320835289053170417268133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52427780385404227223024177 39320835289053170417268133)
    ·
      refine ⟨7372656616697469453237775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39320835289053170417268133 7372656616697469453237775)
      ·
        refine ⟨11058984925046204179856663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372656616697469453237775 11058984925046204179856663)
        ·
          refine ⟨16588477387569306269784995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058984925046204179856663 16588477387569306269784995)
          ·
            refine ⟨24882716081353959404677493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588477387569306269784995 24882716081353959404677493)
            ·
              refine ⟨2332754632626933694188515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24882716081353959404677493 2332754632626933694188515)
              ·
                refine ⟨3499131948940400541282773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332754632626933694188515 3499131948940400541282773)
                ·
                  refine ⟨82010905053290637686315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3499131948940400541282773 82010905053290637686315)
                  ·
                    rfl

theorem cell23_1437441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_1437441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437441 prefixEnd_1437441 := by exact prefixLift 1437441
  have htrace : WordTrace (prefixWord ++ tailWord_1437441) baseStart_1437441 baseEnd_1437441 := by
    simpa [prefixWord, tailWord_1437441, baseEnd_1437441] using wordTrace_append hprefix tailTrace_1437441
  have hstable : (prefixWord ++ tailWord_1437441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437441).length < 2 ^ (prefixWord ++ tailWord_1437441).sum := by decide
  have hdescent : baseEnd_1437441 < baseStart_1437441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437451 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3]
def baseStart_1437451 : Nat := 118140960795 + 1437451 * 2 ^ 59
def prefixEnd_1437451 : Nat := 4983230072969 + 3 ^ 40 * 1437451 * 2
def baseEnd_1437451 : Nat := 738103280286160700051789

theorem tailTrace_1437451 : CollatzResearch.WordTrace tailWord_1437451 prefixEnd_1437451 738103280286160700051789 := by
  unfold tailWord_1437451
  simp only [CollatzResearch.WordTrace]
  refine ⟨52428145115367998930888207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34952096743578665953925471 52428145115367998930888207)
  ·
    refine ⟨78642217673051998396332311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52428145115367998930888207 78642217673051998396332311)
    ·
      refine ⟨117963326509577997594498467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78642217673051998396332311 117963326509577997594498467)
      ·
        refine ⟨176944989764366996391747701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117963326509577997594498467 176944989764366996391747701)
        ·
          refine ⟨16588592790409405911726347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176944989764366996391747701 16588592790409405911726347)
          ·
            refine ⟨24882889185614108867589521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588592790409405911726347 24882889185614108867589521)
            ·
              refine ⟨18662166889210581650692141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24882889185614108867589521 18662166889210581650692141)
              ·
                refine ⟨6998312583453968119009553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18662166889210581650692141 6998312583453968119009553)
                ·
                  refine ⟨5248734437590476089257165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998312583453968119009553 5248734437590476089257165)
                  ·
                    refine ⟨1968275414096428533471437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5248734437590476089257165 1968275414096428533471437)
                    ·
                      refine ⟨738103280286160700051789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968275414096428533471437 738103280286160700051789)
                      ·
                        rfl

theorem cell23_1437451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].length) (baseStart_1437451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437451 prefixEnd_1437451 := by exact prefixLift 1437451
  have htrace : WordTrace (prefixWord ++ tailWord_1437451) baseStart_1437451 baseEnd_1437451 := by
    simpa [prefixWord, tailWord_1437451, baseEnd_1437451] using wordTrace_append hprefix tailTrace_1437451
  have hstable : (prefixWord ++ tailWord_1437451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437451).length < 2 ^ (prefixWord ++ tailWord_1437451).sum := by decide
  have hdescent : baseEnd_1437451 < baseStart_1437451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437452 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_1437452 : Nat := 118140960795 + 1437452 * 2 ^ 59
def prefixEnd_1437452 : Nat := 4983230072969 + 3 ^ 40 * 1437452 * 2
def baseEnd_1437452 : Nat := 738103793766815196139285

theorem tailTrace_1437452 : CollatzResearch.WordTrace tailWord_1437452 prefixEnd_1437452 738103793766815196139285 := by
  unfold tailWord_1437452
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214090794182188050837305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34952121058909584067783073 26214090794182188050837305)
  ·
    refine ⟨19660568095636641038127979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26214090794182188050837305 19660568095636641038127979)
    ·
      refine ⟨29490852143454961557191969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19660568095636641038127979 29490852143454961557191969)
      ·
        refine ⟨22118139107591221167893977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29490852143454961557191969 22118139107591221167893977)
        ·
          refine ⟨16588604330693415875920483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22118139107591221167893977 16588604330693415875920483)
          ·
            refine ⟨24882906496040123813880725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588604330693415875920483 24882906496040123813880725)
            ·
              refine ⟨1166386242001880803775659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24882906496040123813880725 1166386242001880803775659)
              ·
                refine ⟨1749579363002821205663489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166386242001880803775659 1749579363002821205663489)
                ·
                  refine ⟨1312184522252115904247617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1749579363002821205663489 1312184522252115904247617)
                  ·
                    refine ⟨984138391689086928185713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312184522252115904247617 984138391689086928185713)
                    ·
                      refine ⟨738103793766815196139285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984138391689086928185713 738103793766815196139285)
                      ·
                        rfl

theorem cell23_1437452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_1437452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437452 prefixEnd_1437452 := by exact prefixLift 1437452
  have htrace : WordTrace (prefixWord ++ tailWord_1437452) baseStart_1437452 baseEnd_1437452 := by
    simpa [prefixWord, tailWord_1437452, baseEnd_1437452] using wordTrace_append hprefix tailTrace_1437452
  have hstable : (prefixWord ++ tailWord_1437452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437452).length < 2 ^ (prefixWord ++ tailWord_1437452).sum := by decide
  have hdescent : baseEnd_1437452 < baseStart_1437452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437492 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1437492 : Nat := 118140960795 + 1437492 * 2 ^ 59
def prefixEnd_1437492 : Nat := 4983230072969 + 3 ^ 40 * 1437492 * 2
def baseEnd_1437492 : Nat := 82013814776999448848789

theorem tailTrace_1437492 : CollatzResearch.WordTrace tailWord_1437492 prefixEnd_1437492 82013814776999448848789 := by
  unfold tailWord_1437492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214820254109731466565365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34953093672146308622087153 26214820254109731466565365)
  ·
    refine ⟨2457639398822787324990503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26214820254109731466565365 2457639398822787324990503)
    ·
      refine ⟨3686459098234180987485755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457639398822787324990503 3686459098234180987485755)
      ·
        refine ⟨5529688647351271481228633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686459098234180987485755 5529688647351271481228633)
        ·
          refine ⟨4147266485513453610921475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529688647351271481228633 4147266485513453610921475)
          ·
            refine ⟨6220899728270180416382213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147266485513453610921475 6220899728270180416382213)
            ·
              refine ⟨1166418699050658828071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6220899728270180416382213 1166418699050658828071665)
              ·
                refine ⟨874814024287994121053749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166418699050658828071665 874814024287994121053749)
                ·
                  refine ⟨82013814776999448848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874814024287994121053749 82013814776999448848789)
                  ·
                    rfl

theorem cell23_1437492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1437492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437492 prefixEnd_1437492 := by exact prefixLift 1437492
  have htrace : WordTrace (prefixWord ++ tailWord_1437492) baseStart_1437492 baseEnd_1437492 := by
    simpa [prefixWord, tailWord_1437492, baseEnd_1437492] using wordTrace_append hprefix tailTrace_1437492
  have hstable : (prefixWord ++ tailWord_1437492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437492).length < 2 ^ (prefixWord ++ tailWord_1437492).sum := by decide
  have hdescent : baseEnd_1437492 < baseStart_1437492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437525 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1437525 : Nat := 118140960795 + 1437525 * 2 ^ 59
def prefixEnd_1437525 : Nat := 4983230072969 + 3 ^ 40 * 1437525 * 2
def baseEnd_1437525 : Nat := 738141277854593410526449

theorem tailTrace_1437525 : CollatzResearch.WordTrace tailWord_1437525 prefixEnd_1437525 738141277854593410526449 := by
  unfold tailWord_1437525
  simp only [CollatzResearch.WordTrace]
  refine ⟨52430844117099909569082029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34953896078066606379388019 52430844117099909569082029)
  ·
    refine ⟨19661566543912466088405761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52430844117099909569082029 19661566543912466088405761)
    ·
      refine ⟨14746174907934349566304321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19661566543912466088405761 14746174907934349566304321)
      ·
        refine ⟨11059631180950762174728241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14746174907934349566304321 11059631180950762174728241)
        ·
          refine ⟨8294723385713071631046181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11059631180950762174728241 8294723385713071631046181)
          ·
            refine ⟨1555260634821200930821159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8294723385713071631046181 1555260634821200930821159)
            ·
              refine ⟨2332890952231801396231739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555260634821200930821159 2332890952231801396231739)
              ·
                refine ⟨3499336428347702094347609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332890952231801396231739 3499336428347702094347609)
                ·
                  refine ⟨2624502321260776570760707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499336428347702094347609 2624502321260776570760707)
                  ·
                    refine ⟨3936753481891164856141061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624502321260776570760707 3936753481891164856141061)
                    ·
                      refine ⟨738141277854593410526449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3936753481891164856141061 738141277854593410526449)
                      ·
                        rfl

theorem cell23_1437525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1437525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437525 prefixEnd_1437525 := by exact prefixLift 1437525
  have htrace : WordTrace (prefixWord ++ tailWord_1437525) baseStart_1437525 baseEnd_1437525 := by
    simpa [prefixWord, tailWord_1437525, baseEnd_1437525] using wordTrace_append hprefix tailTrace_1437525
  have hstable : (prefixWord ++ tailWord_1437525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437525).length < 2 ^ (prefixWord ++ tailWord_1437525).sum := by decide
  have hdescent : baseEnd_1437525 < baseStart_1437525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437535 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 1, 4]
def baseStart_1437535 : Nat := 118140960795 + 1437535 * 2 ^ 59
def prefixEnd_1437535 : Nat := 4983230072969 + 3 ^ 40 * 1437535 * 2
def baseEnd_1437535 : Nat := 246048804220379457133801

theorem tailTrace_1437535 : CollatzResearch.WordTrace tailWord_1437535 prefixEnd_1437535 246048804220379457133801 := by
  unfold tailWord_1437535
  simp only [CollatzResearch.WordTrace]
  refine ⟨52431208847063681276946059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34954139231375787517964039 52431208847063681276946059)
  ·
    refine ⟨78646813270595521915419089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52431208847063681276946059 78646813270595521915419089)
    ·
      refine ⟨58985109952946641436564317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78646813270595521915419089 58985109952946641436564317)
      ·
        refine ⟨22119416232354990538711619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58985109952946641436564317 22119416232354990538711619)
        ·
          refine ⟨33179124348532485808067429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22119416232354990538711619 33179124348532485808067429)
          ·
            refine ⟨6221085815349841089012643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33179124348532485808067429 6221085815349841089012643)
            ·
              refine ⟨9331628723024761633518965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221085815349841089012643 9331628723024761633518965)
              ·
                refine ⟨874840192783571403142403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9331628723024761633518965 874840192783571403142403)
                ·
                  refine ⟨1312260289175357104713605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874840192783571403142403 1312260289175357104713605)
                  ·
                    refine ⟨246048804220379457133801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312260289175357104713605 246048804220379457133801)
                    ·
                      rfl

theorem cell23_1437535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_1437535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437535 prefixEnd_1437535 := by exact prefixLift 1437535
  have htrace : WordTrace (prefixWord ++ tailWord_1437535) baseStart_1437535 baseEnd_1437535 := by
    simpa [prefixWord, tailWord_1437535, baseEnd_1437535] using wordTrace_append hprefix tailTrace_1437535
  have hstable : (prefixWord ++ tailWord_1437535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437535).length < 2 ^ (prefixWord ++ tailWord_1437535).sum := by decide
  have hdescent : baseEnd_1437535 < baseStart_1437535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437538 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1437538 : Nat := 118140960795 + 1437538 * 2 ^ 59
def prefixEnd_1437538 : Nat := 4983230072969 + 3 ^ 40 * 1437538 * 2
def baseEnd_1437538 : Nat := 738147953103101859663889

theorem tailTrace_1437538 : CollatzResearch.WordTrace tailWord_1437538 prefixEnd_1437538 738147953103101859663889 := by
  unfold tailWord_1437538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107829566513203197326317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34954212177368541859536845 13107829566513203197326317)
  ·
    refine ⟨4915436087442451198997369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13107829566513203197326317 4915436087442451198997369)
    ·
      refine ⟨3686577065581838399248027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915436087442451198997369 3686577065581838399248027)
      ·
        refine ⟨5529865598372757598872041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686577065581838399248027 5529865598372757598872041)
        ·
          refine ⟨4147399198779568199154031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529865598372757598872041 4147399198779568199154031)
          ·
            refine ⟨6221098798169352298731047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147399198779568199154031 6221098798169352298731047)
            ·
              refine ⟨9331648197254028448096571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221098798169352298731047 9331648197254028448096571)
              ·
                refine ⟨13997472295881042672144857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331648197254028448096571 13997472295881042672144857)
                ·
                  refine ⟨10498104221910782004108643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13997472295881042672144857 10498104221910782004108643)
                  ·
                    refine ⟨15747156332866173006162965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10498104221910782004108643 15747156332866173006162965)
                    ·
                      refine ⟨738147953103101859663889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15747156332866173006162965 738147953103101859663889)
                      ·
                        rfl

theorem cell23_1437538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1437538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437538 prefixEnd_1437538 := by exact prefixLift 1437538
  have htrace : WordTrace (prefixWord ++ tailWord_1437538) baseStart_1437538 baseEnd_1437538 := by
    simpa [prefixWord, tailWord_1437538, baseEnd_1437538] using wordTrace_append hprefix tailTrace_1437538
  have hstable : (prefixWord ++ tailWord_1437538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437538).length < 2 ^ (prefixWord ++ tailWord_1437538).sum := by decide
  have hdescent : baseEnd_1437538 < baseStart_1437538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437548 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 6]
def baseStart_1437548 : Nat := 118140960795 + 1437548 * 2 ^ 59
def prefixEnd_1437548 : Nat := 4983230072969 + 3 ^ 40 * 1437548 * 2
def baseEnd_1437548 : Nat := 82017009767738535615427

theorem tailTrace_1437548 : CollatzResearch.WordTrace tailWord_1437548 prefixEnd_1437548 82017009767738535615427 := by
  unfold tailWord_1437548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26215841498008292248584649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34954455330677722998112865 26215841498008292248584649)
  ·
    refine ⟨19661881123506219186438487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26215841498008292248584649 19661881123506219186438487)
    ·
      refine ⟨29492821685259328779657731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661881123506219186438487 29492821685259328779657731)
      ·
        refine ⟨44239232527888993169486597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29492821685259328779657731 44239232527888993169486597)
        ·
          refine ⟨8294856098979186219278737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44239232527888993169486597 8294856098979186219278737)
          ·
            refine ⟨6221142074234389664459053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294856098979186219278737 6221142074234389664459053)
            ·
              refine ⟨2332928277837896124172145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6221142074234389664459053 2332928277837896124172145)
              ·
                refine ⟨1749696208378422093129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332928277837896124172145 1749696208378422093129109)
                ·
                  refine ⟨82017009767738535615427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1749696208378422093129109 82017009767738535615427)
                  ·
                    rfl

theorem cell23_1437548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_1437548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437548 prefixEnd_1437548 := by exact prefixLift 1437548
  have htrace : WordTrace (prefixWord ++ tailWord_1437548) baseStart_1437548 baseEnd_1437548 := by
    simpa [prefixWord, tailWord_1437548, baseEnd_1437548] using wordTrace_append hprefix tailTrace_1437548
  have hstable : (prefixWord ++ tailWord_1437548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437548).length < 2 ^ (prefixWord ++ tailWord_1437548).sum := by decide
  have hdescent : baseEnd_1437548 < baseStart_1437548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437568 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2]
def baseStart_1437568 : Nat := 118140960795 + 1437568 * 2 ^ 59
def prefixEnd_1437568 : Nat := 4983230072969 + 3 ^ 40 * 1437568 * 2
def baseEnd_1437568 : Nat := 738163357522736742288751

theorem tailTrace_1437568 : CollatzResearch.WordTrace tailWord_1437568 prefixEnd_1437568 738163357522736742288751 := by
  unfold tailWord_1437568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26216206227972063956448679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34954941637296085275264905 26216206227972063956448679)
  ·
    refine ⟨39324309341958095934673019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26216206227972063956448679 39324309341958095934673019)
    ·
      refine ⟨58986464012937143902009529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39324309341958095934673019 58986464012937143902009529)
      ·
        refine ⟨44239848009702857926507147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58986464012937143902009529 44239848009702857926507147)
        ·
          refine ⟨66359772014554286889760721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44239848009702857926507147 66359772014554286889760721)
          ·
            refine ⟨49769829010915715167320541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66359772014554286889760721 49769829010915715167320541)
            ·
              refine ⟨18663685879093393187745203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49769829010915715167320541 18663685879093393187745203)
              ·
                refine ⟨27995528818640089781617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18663685879093393187745203 27995528818640089781617805)
                ·
                  refine ⟨10498323306990033668106677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27995528818640089781617805 10498323306990033668106677)
                  ·
                    refine ⟨984217810030315656385001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10498323306990033668106677 984217810030315656385001)
                    ·
                      refine ⟨738163357522736742288751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984217810030315656385001 738163357522736742288751)
                      ·
                        rfl

theorem cell23_1437568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_1437568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437568 prefixEnd_1437568 := by exact prefixLift 1437568
  have htrace : WordTrace (prefixWord ++ tailWord_1437568) baseStart_1437568 baseEnd_1437568 := by
    simpa [prefixWord, tailWord_1437568, baseEnd_1437568] using wordTrace_append hprefix tailTrace_1437568
  have hstable : (prefixWord ++ tailWord_1437568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437568).length < 2 ^ (prefixWord ++ tailWord_1437568).sum := by decide
  have hdescent : baseEnd_1437568 < baseStart_1437568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
