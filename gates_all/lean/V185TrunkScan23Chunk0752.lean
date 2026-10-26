import V185TrunkScan23Chunk0751

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4446710 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4446710 : Nat := 118140960795 + 4446710 * 2 ^ 59
def prefixEnd_4446710 : Nat := 4983230072969 + 3 ^ 40 * 4446710 * 2
def baseEnd_4446710 : Nat := 2283299561154402460374959

theorem tailTrace_4446710 : CollatzResearch.WordTrace tailWord_4446710 prefixEnd_4446710 2283299561154402460374959 := by
  unfold tailWord_4446710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136552357521036403199599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108123225146891054967462389 10136552357521036403199599)
  ·
    refine ⟨15204828536281554604799399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10136552357521036403199599 15204828536281554604799399)
    ·
      refine ⟨22807242804422331907199099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15204828536281554604799399 22807242804422331907199099)
      ·
        refine ⟨34210864206633497860798649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22807242804422331907199099 34210864206633497860798649)
        ·
          refine ⟨25658148154975123395598987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34210864206633497860798649 25658148154975123395598987)
          ·
            refine ⟨38487222232462685093398481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25658148154975123395598987 38487222232462685093398481)
            ·
              refine ⟨28865416674347013820048861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38487222232462685093398481 28865416674347013820048861)
              ·
                refine ⟨10824531252880130182518323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28865416674347013820048861 10824531252880130182518323)
                ·
                  refine ⟨16236796879320195273777485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10824531252880130182518323 16236796879320195273777485)
                  ·
                    refine ⟨6088798829745073227666557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16236796879320195273777485 6088798829745073227666557)
                    ·
                      refine ⟨2283299561154402460374959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088798829745073227666557 2283299561154402460374959)
                      ·
                        rfl

theorem cell23_4446710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4446710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446710 prefixEnd_4446710 := by exact prefixLift 4446710
  have htrace : WordTrace (prefixWord ++ tailWord_4446710) baseStart_4446710 baseEnd_4446710 := by
    simpa [prefixWord, tailWord_4446710, baseEnd_4446710] using wordTrace_append hprefix tailTrace_4446710
  have hstable : (prefixWord ++ tailWord_4446710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446710).length < 2 ^ (prefixWord ++ tailWord_4446710).sum := by decide
  have hdescent : baseEnd_4446710 < baseStart_4446710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446716 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_4446716 : Nat := 118140960795 + 4446716 * 2 ^ 59
def prefixEnd_4446716 : Nat := 4983230072969 + 3 ^ 40 * 4446716 * 2
def baseEnd_4446716 : Nat := 2283302642038329436899931

theorem tailTrace_4446716 : CollatzResearch.WordTrace tailWord_4446716 prefixEnd_4446716 2283302642038329436899931 := by
  unfold tailWord_4446716
  simp only [CollatzResearch.WordTrace]
  refine ⟨81092528279157422737956001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108123371038876563650608001 81092528279157422737956001)
  ·
    refine ⟨60819396209368067053467001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81092528279157422737956001 60819396209368067053467001)
    ·
      refine ⟨45614547157026050290100251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60819396209368067053467001 45614547157026050290100251)
      ·
        refine ⟨68421820735539075435150377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45614547157026050290100251 68421820735539075435150377)
        ·
          refine ⟨51316365551654306576362783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68421820735539075435150377 51316365551654306576362783)
          ·
            refine ⟨76974548327481459864544175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51316365551654306576362783 76974548327481459864544175)
            ·
              refine ⟨115461822491222189796816263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76974548327481459864544175 115461822491222189796816263)
              ·
                refine ⟨173192733736833284695224395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115461822491222189796816263 173192733736833284695224395)
                ·
                  refine ⟨259789100605249927042836593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173192733736833284695224395 259789100605249927042836593)
                  ·
                    refine ⟨194841825453937445282127445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259789100605249927042836593 194841825453937445282127445)
                    ·
                      refine ⟨2283302642038329436899931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194841825453937445282127445 2283302642038329436899931)
                      ·
                        rfl

theorem cell23_4446716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_4446716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446716 prefixEnd_4446716 := by exact prefixLift 4446716
  have htrace : WordTrace (prefixWord ++ tailWord_4446716) baseStart_4446716 baseEnd_4446716 := by
    simpa [prefixWord, tailWord_4446716, baseEnd_4446716] using wordTrace_append hprefix tailTrace_4446716
  have hstable : (prefixWord ++ tailWord_4446716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446716).length < 2 ^ (prefixWord ++ tailWord_4446716).sum := by decide
  have hdescent : baseEnd_4446716 < baseStart_4446716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446736 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_4446736 : Nat := 118140960795 + 4446736 * 2 ^ 59
def prefixEnd_4446736 : Nat := 4983230072969 + 3 ^ 40 * 4446736 * 2
def baseEnd_4446736 : Nat := 2283312911651419358649839

theorem tailTrace_4446736 : CollatzResearch.WordTrace tailWord_4446736 prefixEnd_4446736 2283312911651419358649839 := by
  unfold tailWord_4446736
  simp only [CollatzResearch.WordTrace]
  refine ⟨81092893009121194445820031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108123857345494925927760041 81092893009121194445820031)
  ·
    refine ⟨121639339513681791668730047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81092893009121194445820031 121639339513681791668730047)
    ·
      refine ⟨182459009270522687503095071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121639339513681791668730047 182459009270522687503095071)
      ·
        refine ⟨273688513905784031254642607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182459009270522687503095071 273688513905784031254642607)
        ·
          refine ⟨410532770858676046881963911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273688513905784031254642607 410532770858676046881963911)
          ·
            refine ⟨615799156288014070322945867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410532770858676046881963911 615799156288014070322945867)
            ·
              refine ⟨923698734432021105484418801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615799156288014070322945867 923698734432021105484418801)
              ·
                refine ⟨692774050824015829113314101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923698734432021105484418801 692774050824015829113314101)
                ·
                  refine ⟨64947567264751483979373197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 692774050824015829113314101 64947567264751483979373197)
                  ·
                    refine ⟨24355337724281806492264949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64947567264751483979373197 24355337724281806492264949)
                    ·
                      refine ⟨2283312911651419358649839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24355337724281806492264949 2283312911651419358649839)
                      ·
                        rfl

theorem cell23_4446736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_4446736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446736 prefixEnd_4446736 := by exact prefixLift 4446736
  have htrace : WordTrace (prefixWord ++ tailWord_4446736) baseStart_4446736 baseEnd_4446736 := by
    simpa [prefixWord, tailWord_4446736, baseEnd_4446736] using wordTrace_append hprefix tailTrace_4446736
  have hstable : (prefixWord ++ tailWord_4446736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446736).length < 2 ^ (prefixWord ++ tailWord_4446736).sum := by decide
  have hdescent : baseEnd_4446736 < baseStart_4446736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446753 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4446753 : Nat := 118140960795 + 4446753 * 2 ^ 59
def prefixEnd_4446753 : Nat := 4983230072969 + 3 ^ 40 * 4446753 * 2
def baseEnd_4446753 : Nat := 2283321640822545792137261

theorem tailTrace_4446753 : CollatzResearch.WordTrace tailWord_4446753 prefixEnd_4446753 2283321640822545792137261 := by
  unfold tailWord_4446753
  simp only [CollatzResearch.WordTrace]
  refine ⟨162186406059180800795008913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108124270706120533863339275 162186406059180800795008913)
  ·
    refine ⟨121639804544385600596256685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162186406059180800795008913 121639804544385600596256685)
    ·
      refine ⟨45614926704144600223596257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121639804544385600596256685 45614926704144600223596257)
      ·
        refine ⟨34211195028108450167697193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45614926704144600223596257 34211195028108450167697193)
        ·
          refine ⟨25658396271081337625772895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34211195028108450167697193 25658396271081337625772895)
          ·
            refine ⟨38487594406622006438659343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25658396271081337625772895 38487594406622006438659343)
            ·
              refine ⟨57731391609933009657989015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38487594406622006438659343 57731391609933009657989015)
              ·
                refine ⟨86597087414899514486983523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57731391609933009657989015 86597087414899514486983523)
                ·
                  refine ⟨129895631122349271730475285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86597087414899514486983523 129895631122349271730475285)
                  ·
                    refine ⟨6088857708860122112366029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129895631122349271730475285 6088857708860122112366029)
                    ·
                      refine ⟨2283321640822545792137261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088857708860122112366029 2283321640822545792137261)
                      ·
                        rfl

theorem cell23_4446753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4446753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446753 prefixEnd_4446753 := by exact prefixLift 4446753
  have htrace : WordTrace (prefixWord ++ tailWord_4446753) baseStart_4446753 baseEnd_4446753 := by
    simpa [prefixWord, tailWord_4446753, baseEnd_4446753] using wordTrace_append hprefix tailTrace_4446753
  have hstable : (prefixWord ++ tailWord_4446753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446753).length < 2 ^ (prefixWord ++ tailWord_4446753).sum := by decide
  have hdescent : baseEnd_4446753 < baseStart_4446753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446760 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4446760 : Nat := 118140960795 + 4446760 * 2 ^ 59
def prefixEnd_4446760 : Nat := 4983230072969 + 3 ^ 40 * 4446760 * 2
def baseEnd_4446760 : Nat := 761108411729042421583243

theorem tailTrace_4446760 : CollatzResearch.WordTrace tailWord_4446760 prefixEnd_4446760 761108411729042421583243 := by
  unfold tailWord_4446760
  simp only [CollatzResearch.WordTrace]
  refine ⟨81093330685077720495256867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108124440913436960660342489 81093330685077720495256867)
  ·
    refine ⟨121639996027616580742885301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81093330685077720495256867 121639996027616580742885301)
    ·
      refine ⟨11403749627589054444645497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121639996027616580742885301 11403749627589054444645497)
      ·
        refine ⟨8552812220691790833484123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11403749627589054444645497 8552812220691790833484123)
        ·
          refine ⟨12829218331037686250226185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552812220691790833484123 12829218331037686250226185)
          ·
            refine ⟨9621913748278264687669639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12829218331037686250226185 9621913748278264687669639)
            ·
              refine ⟨14432870622417397031504459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9621913748278264687669639 14432870622417397031504459)
              ·
                refine ⟨21649305933626095547256689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14432870622417397031504459 21649305933626095547256689)
                ·
                  refine ⟨16236979450219571660442517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21649305933626095547256689 16236979450219571660442517)
                  ·
                    refine ⟨761108411729042421583243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16236979450219571660442517 761108411729042421583243)
                    ·
                      rfl

theorem cell23_4446760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4446760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446760 prefixEnd_4446760 := by exact prefixLift 4446760
  have htrace : WordTrace (prefixWord ++ tailWord_4446760) baseStart_4446760 baseEnd_4446760 := by
    simpa [prefixWord, tailWord_4446760, baseEnd_4446760] using wordTrace_append hprefix tailTrace_4446760
  have hstable : (prefixWord ++ tailWord_4446760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446760).length < 2 ^ (prefixWord ++ tailWord_4446760).sum := by decide
  have hdescent : baseEnd_4446760 < baseStart_4446760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446773 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 7]
def baseStart_4446773 : Nat := 118140960795 + 4446773 * 2 ^ 59
def prefixEnd_4446773 : Nat := 4983230072969 + 3 ^ 40 * 4446773 * 2
def baseEnd_4446773 : Nat := 253703545603959523765241

theorem tailTrace_4446773 : CollatzResearch.WordTrace tailWord_4446773 prefixEnd_4446773 253703545603959523765241 := by
  unfold tailWord_4446773
  simp only [CollatzResearch.WordTrace]
  refine ⟨162187135519108344210736973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108124757012738896140491315 162187135519108344210736973)
  ·
    refine ⟨60820175819665629079026365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162187135519108344210736973 60820175819665629079026365)
    ·
      refine ⟨22807565932374610904634887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60820175819665629079026365 22807565932374610904634887)
      ·
        refine ⟨34211348898561916356952331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22807565932374610904634887 34211348898561916356952331)
        ·
          refine ⟨51317023347842874535428497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34211348898561916356952331 51317023347842874535428497)
          ·
            refine ⟨38487767510882155901571373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51317023347842874535428497 38487767510882155901571373)
            ·
              refine ⟨14432912816580808463089265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38487767510882155901571373 14432912816580808463089265)
              ·
                refine ⟨10824684612435606347316949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14432912816580808463089265 10824684612435606347316949)
                ·
                  refine ⟨253703545603959523765241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10824684612435606347316949 253703545603959523765241)
                  ·
                    rfl

theorem cell23_4446773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_4446773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446773 prefixEnd_4446773 := by exact prefixLift 4446773
  have htrace : WordTrace (prefixWord ++ tailWord_4446773) baseStart_4446773 baseEnd_4446773 := by
    simpa [prefixWord, tailWord_4446773, baseEnd_4446773] using wordTrace_append hprefix tailTrace_4446773
  have hstable : (prefixWord ++ tailWord_4446773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446773).length < 2 ^ (prefixWord ++ tailWord_4446773).sum := by decide
  have hdescent : baseEnd_4446773 < baseStart_4446773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446783 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_4446783 : Nat := 118140960795 + 4446783 * 2 ^ 59
def prefixEnd_4446783 : Nat := 4983230072969 + 3 ^ 40 * 4446783 * 2
def baseEnd_4446783 : Nat := 2283337045242180674762123

theorem tailTrace_4446783 : CollatzResearch.WordTrace tailWord_4446783 prefixEnd_4446783 2283337045242180674762123 := by
  unfold tailWord_4446783
  simp only [CollatzResearch.WordTrace]
  refine ⟨162187500249072115918601003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108125000166048077279067335 162187500249072115918601003)
  ·
    refine ⟨243281250373608173877901505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162187500249072115918601003 243281250373608173877901505)
    ·
      refine ⟨182460937780206130408426129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243281250373608173877901505 182460937780206130408426129)
      ·
        refine ⟨136845703335154597806319597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182460937780206130408426129 136845703335154597806319597)
        ·
          refine ⟨51317138750682974177369849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136845703335154597806319597 51317138750682974177369849)
          ·
            refine ⟨38487854063012230633027387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51317138750682974177369849 38487854063012230633027387)
            ·
              refine ⟨57731781094518345949541081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38487854063012230633027387 57731781094518345949541081)
              ·
                refine ⟨43298835820888759462155811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57731781094518345949541081 43298835820888759462155811)
                ·
                  refine ⟨64948253731333139193233717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43298835820888759462155811 64948253731333139193233717)
                  ·
                    refine ⟨6088898787312481799365661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64948253731333139193233717 6088898787312481799365661)
                    ·
                      refine ⟨2283337045242180674762123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6088898787312481799365661 2283337045242180674762123)
                      ·
                        rfl

theorem cell23_4446783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_4446783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446783 prefixEnd_4446783 := by exact prefixLift 4446783
  have htrace : WordTrace (prefixWord ++ tailWord_4446783) baseStart_4446783 baseEnd_4446783 := by
    simpa [prefixWord, tailWord_4446783, baseEnd_4446783] using wordTrace_append hprefix tailTrace_4446783
  have hstable : (prefixWord ++ tailWord_4446783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446783).length < 2 ^ (prefixWord ++ tailWord_4446783).sum := by decide
  have hdescent : baseEnd_4446783 < baseStart_4446783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446788 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4446788 : Nat := 118140960795 + 4446788 * 2 ^ 59
def prefixEnd_4446788 : Nat := 4983230072969 + 3 ^ 40 * 4446788 * 2
def baseEnd_4446788 : Nat := 2283339612645453155199601

theorem tailTrace_4446788 : CollatzResearch.WordTrace tailWord_4446788 prefixEnd_4446788 2283339612645453155199601 := by
  unfold tailWord_4446788
  simp only [CollatzResearch.WordTrace]
  refine ⟨81093841307027000886266509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108125121742702667848355345 81093841307027000886266509)
  ·
    refine ⟨30410190490135125332349941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81093841307027000886266509 30410190490135125332349941)
    ·
      refine ⟨2850955358450167999907807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30410190490135125332349941 2850955358450167999907807)
      ·
        refine ⟨4276433037675251999861711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850955358450167999907807 4276433037675251999861711)
        ·
          refine ⟨6414649556512877999792567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276433037675251999861711 6414649556512877999792567)
          ·
            refine ⟨9621974334769316999688851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414649556512877999792567 9621974334769316999688851)
            ·
              refine ⟨14432961502153975499533277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9621974334769316999688851 14432961502153975499533277)
              ·
                refine ⟨5412360563307740812324979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14432961502153975499533277 5412360563307740812324979)
                ·
                  refine ⟨8118540844961611218487469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412360563307740812324979 8118540844961611218487469)
                  ·
                    refine ⟨3044452816860604206932801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8118540844961611218487469 3044452816860604206932801)
                    ·
                      refine ⟨2283339612645453155199601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044452816860604206932801 2283339612645453155199601)
                      ·
                        rfl

theorem cell23_4446788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4446788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446788 prefixEnd_4446788 := by exact prefixLift 4446788
  have htrace : WordTrace (prefixWord ++ tailWord_4446788) baseStart_4446788 baseEnd_4446788 := by
    simpa [prefixWord, tailWord_4446788, baseEnd_4446788] using wordTrace_append hprefix tailTrace_4446788
  have hstable : (prefixWord ++ tailWord_4446788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446788).length < 2 ^ (prefixWord ++ tailWord_4446788).sum := by decide
  have hdescent : baseEnd_4446788 < baseStart_4446788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446818 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4446818 : Nat := 118140960795 + 4446818 * 2 ^ 59
def prefixEnd_4446818 : Nat := 4983230072969 + 3 ^ 40 * 4446818 * 2
def baseEnd_4446818 : Nat := 2283355017065088037824463

theorem tailTrace_4446818 : CollatzResearch.WordTrace tailWord_4446818 prefixEnd_4446818 2283355017065088037824463 := by
  unfold tailWord_4446818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40547194200986329224031277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108125851202630211264083405 40547194200986329224031277)
  ·
    refine ⟨15205197825369873459011729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40547194200986329224031277 15205197825369873459011729)
    ·
      refine ⟨11403898369027405094258797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15205197825369873459011729 11403898369027405094258797)
      ·
        refine ⟨4276461888385276910347049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11403898369027405094258797 4276461888385276910347049)
        ·
          refine ⟨3207346416288957682760287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4276461888385276910347049 3207346416288957682760287)
          ·
            refine ⟨4811019624433436524140431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207346416288957682760287 4811019624433436524140431)
            ·
              refine ⟨7216529436650154786210647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811019624433436524140431 7216529436650154786210647)
              ·
                refine ⟨10824794154975232179315971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7216529436650154786210647 10824794154975232179315971)
                ·
                  refine ⟨16237191232462848268973957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10824794154975232179315971 16237191232462848268973957)
                  ·
                    refine ⟨3044473356086784050432617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16237191232462848268973957 3044473356086784050432617)
                    ·
                      refine ⟨2283355017065088037824463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044473356086784050432617 2283355017065088037824463)
                      ·
                        rfl

theorem cell23_4446818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4446818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446818 prefixEnd_4446818 := by exact prefixLift 4446818
  have htrace : WordTrace (prefixWord ++ tailWord_4446818) baseStart_4446818 baseEnd_4446818 := by
    simpa [prefixWord, tailWord_4446818, baseEnd_4446818] using wordTrace_append hprefix tailTrace_4446818
  have hstable : (prefixWord ++ tailWord_4446818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446818).length < 2 ^ (prefixWord ++ tailWord_4446818).sum := by decide
  have hdescent : baseEnd_4446818 < baseStart_4446818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446894 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4446894 : Nat := 118140960795 + 4446894 * 2 ^ 59
def prefixEnd_4446894 : Nat := 4983230072969 + 3 ^ 40 * 4446894 * 2
def baseEnd_4446894 : Nat := 2283394041594829740474113

theorem tailTrace_4446894 : CollatzResearch.WordTrace tailWord_4446894 prefixEnd_4446894 2283394041594829740474113 := by
  unfold tailWord_4446894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20273943593958747734486467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108127699167779987917261157 20273943593958747734486467)
  ·
    refine ⟨30410915390938121601729701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20273943593958747734486467 30410915390938121601729701)
    ·
      refine ⟨5702046635800897800324319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30410915390938121601729701 5702046635800897800324319)
      ·
        refine ⟨8553069953701346700486479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702046635800897800324319 8553069953701346700486479)
        ·
          refine ⟨12829604930552020050729719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553069953701346700486479 12829604930552020050729719)
          ·
            refine ⟨19244407395828030076094579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12829604930552020050729719 19244407395828030076094579)
            ·
              refine ⟨28866611093742045114141869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19244407395828030076094579 28866611093742045114141869)
              ·
                refine ⟨10824979160153266917803201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28866611093742045114141869 10824979160153266917803201)
                ·
                  refine ⟨8118734370114950188352401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10824979160153266917803201 8118734370114950188352401)
                  ·
                    refine ⟨6089050777586212641264301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8118734370114950188352401 6089050777586212641264301)
                    ·
                      refine ⟨2283394041594829740474113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6089050777586212641264301 2283394041594829740474113)
                      ·
                        rfl

theorem cell23_4446894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4446894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446894 prefixEnd_4446894 := by exact prefixLift 4446894
  have htrace : WordTrace (prefixWord ++ tailWord_4446894) baseStart_4446894 baseEnd_4446894 := by
    simpa [prefixWord, tailWord_4446894, baseEnd_4446894] using wordTrace_append hprefix tailTrace_4446894
  have hstable : (prefixWord ++ tailWord_4446894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446894).length < 2 ^ (prefixWord ++ tailWord_4446894).sum := by decide
  have hdescent : baseEnd_4446894 < baseStart_4446894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446947 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4446947 : Nat := 118140960795 + 4446947 * 2 ^ 59
def prefixEnd_4446947 : Nat := 4983230072969 + 3 ^ 40 * 4446947 * 2
def baseEnd_4446947 : Nat := 2283421256069518033111369

theorem tailTrace_4446947 : CollatzResearch.WordTrace tailWord_4446947 prefixEnd_4446947 2283421256069518033111369 := by
  unfold tailWord_4446947
  simp only [CollatzResearch.WordTrace]
  refine ⟨162193481820477971927571095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108128987880318647951714063 162193481820477971927571095)
  ·
    refine ⟨243290222730716957891356643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162193481820477971927571095 243290222730716957891356643)
    ·
      refine ⟨364935334096075436837034965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243290222730716957891356643 364935334096075436837034965)
      ·
        refine ⟨8553171892876768050868007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 364935334096075436837034965 8553171892876768050868007)
        ·
          refine ⟨12829757839315152076302011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553171892876768050868007 12829757839315152076302011)
          ·
            refine ⟨19244636758972728114453017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12829757839315152076302011 19244636758972728114453017)
            ·
              refine ⟨14433477569229546085839763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19244636758972728114453017 14433477569229546085839763)
              ·
                refine ⟨21650216353844319128759645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14433477569229546085839763 21650216353844319128759645)
                ·
                  refine ⟨8118831132691619673284867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21650216353844319128759645 8118831132691619673284867)
                  ·
                    refine ⟨12178246699037429509927301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8118831132691619673284867 12178246699037429509927301)
                    ·
                      refine ⟨2283421256069518033111369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12178246699037429509927301 2283421256069518033111369)
                      ·
                        rfl

theorem cell23_4446947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4446947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446947 prefixEnd_4446947 := by exact prefixLift 4446947
  have htrace : WordTrace (prefixWord ++ tailWord_4446947) baseStart_4446947 baseEnd_4446947 := by
    simpa [prefixWord, tailWord_4446947, baseEnd_4446947] using wordTrace_append hprefix tailTrace_4446947
  have hstable : (prefixWord ++ tailWord_4446947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446947).length < 2 ^ (prefixWord ++ tailWord_4446947).sum := by decide
  have hdescent : baseEnd_4446947 < baseStart_4446947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446953 : List Nat := [1, 2, 1, 1, 1, 2, 4, 11]
def baseStart_4446953 : Nat := 118140960795 + 4446953 * 2 ^ 59
def prefixEnd_4446953 : Nat := 4983230072969 + 3 ^ 40 * 4446953 * 2
def baseEnd_4446953 : Nat := 84571271739016481838383

theorem tailTrace_4446953 : CollatzResearch.WordTrace tailWord_4446953 prefixEnd_4446953 84571271739016481838383 := by
  unfold tailWord_4446953
  simp only [CollatzResearch.WordTrace]
  refine ⟨162193700658456234952289513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108129133772304156634859675 162193700658456234952289513)
  ·
    refine ⟨121645275493842176214217135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162193700658456234952289513 121645275493842176214217135)
    ·
      refine ⟨182467913240763264321325703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121645275493842176214217135 182467913240763264321325703)
      ·
        refine ⟨273701869861144896481988555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182467913240763264321325703 273701869861144896481988555)
        ·
          refine ⟨410552804791717344722982833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273701869861144896481988555 410552804791717344722982833)
          ·
            refine ⟨307914603593788008542237125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410552804791717344722982833 307914603593788008542237125)
            ·
              refine ⟨57733988173835251601669461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307914603593788008542237125 57733988173835251601669461)
              ·
                refine ⟨84571271739016481838383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57733988173835251601669461 84571271739016481838383)
                ·
                  rfl

theorem cell23_4446953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 11].length) (baseStart_4446953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446953 prefixEnd_4446953 := by exact prefixLift 4446953
  have htrace : WordTrace (prefixWord ++ tailWord_4446953) baseStart_4446953 baseEnd_4446953 := by
    simpa [prefixWord, tailWord_4446953, baseEnd_4446953] using wordTrace_append hprefix tailTrace_4446953
  have hstable : (prefixWord ++ tailWord_4446953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446953).length < 2 ^ (prefixWord ++ tailWord_4446953).sum := by decide
  have hdescent : baseEnd_4446953 < baseStart_4446953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446957 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_4446957 : Nat := 118140960795 + 4446957 * 2 ^ 59
def prefixEnd_4446957 : Nat := 4983230072969 + 3 ^ 40 * 4446957 * 2
def baseEnd_4446957 : Nat := 761142130292020997995441

theorem tailTrace_4446957 : CollatzResearch.WordTrace tailWord_4446957 prefixEnd_4446957 761142130292020997995441 := by
  unfold tailWord_4446957
  simp only [CollatzResearch.WordTrace]
  refine ⟨162193846550441743635435125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108129231033627829090290083 162193846550441743635435125)
  ·
    refine ⟨15205673114103913465822043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162193846550441743635435125 15205673114103913465822043)
    ·
      refine ⟨22808509671155870198733065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15205673114103913465822043 22808509671155870198733065)
      ·
        refine ⟨17106382253366902649049799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22808509671155870198733065 17106382253366902649049799)
        ·
          refine ⟨25659573380050353973574699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17106382253366902649049799 25659573380050353973574699)
          ·
            refine ⟨38489360070075530960362049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25659573380050353973574699 38489360070075530960362049)
            ·
              refine ⟨28867020052556648220271537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38489360070075530960362049 28867020052556648220271537)
              ·
                refine ⟨21650265039417486165203653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28867020052556648220271537 21650265039417486165203653)
                ·
                  refine ⟨4059424694890778655975685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21650265039417486165203653 4059424694890778655975685)
                  ·
                    refine ⟨761142130292020997995441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059424694890778655975685 761142130292020997995441)
                    ·
                      rfl

theorem cell23_4446957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_4446957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446957 prefixEnd_4446957 := by exact prefixLift 4446957
  have htrace : WordTrace (prefixWord ++ tailWord_4446957) baseStart_4446957 baseEnd_4446957 := by
    simpa [prefixWord, tailWord_4446957, baseEnd_4446957] using wordTrace_append hprefix tailTrace_4446957
  have hstable : (prefixWord ++ tailWord_4446957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446957).length < 2 ^ (prefixWord ++ tailWord_4446957).sum := by decide
  have hdescent : baseEnd_4446957 < baseStart_4446957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446960 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_4446960 : Nat := 118140960795 + 4446960 * 2 ^ 59
def prefixEnd_4446960 : Nat := 4983230072969 + 3 ^ 40 * 4446960 * 2
def baseEnd_4446960 : Nat := 2283427931318026482248809

theorem tailTrace_4446960 : CollatzResearch.WordTrace tailWord_4446960 prefixEnd_4446960 2283427931318026482248809 := by
  unfold tailWord_4446960
  simp only [CollatzResearch.WordTrace]
  refine ⟨81096977984715437573897167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108129303979620583431862889 81096977984715437573897167)
  ·
    refine ⟨121645466977073156360845751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81096977984715437573897167 121645466977073156360845751)
    ·
      refine ⟨182468200465609734541268627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121645466977073156360845751 182468200465609734541268627)
      ·
        refine ⟨273702300698414601811902941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182468200465609734541268627 273702300698414601811902941)
        ·
          refine ⟨102638362761905475679463603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273702300698414601811902941 102638362761905475679463603)
          ·
            refine ⟨153957544142858213519195405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102638362761905475679463603 153957544142858213519195405)
            ·
              refine ⟨57734079053571830069698277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153957544142858213519195405 57734079053571830069698277)
              ·
                refine ⟨10825139822544718138068427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57734079053571830069698277 10825139822544718138068427)
                ·
                  refine ⟨16237709733817077207102641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10825139822544718138068427 16237709733817077207102641)
                  ·
                    refine ⟨12178282300362807905326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16237709733817077207102641 12178282300362807905326981)
                    ·
                      refine ⟨2283427931318026482248809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12178282300362807905326981 2283427931318026482248809)
                      ·
                        rfl

theorem cell23_4446960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_4446960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446960 prefixEnd_4446960 := by exact prefixLift 4446960
  have htrace : WordTrace (prefixWord ++ tailWord_4446960) baseStart_4446960 baseEnd_4446960 := by
    simpa [prefixWord, tailWord_4446960, baseEnd_4446960] using wordTrace_append hprefix tailTrace_4446960
  have hstable : (prefixWord ++ tailWord_4446960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446960).length < 2 ^ (prefixWord ++ tailWord_4446960).sum := by decide
  have hdescent : baseEnd_4446960 < baseStart_4446960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446974 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4446974 : Nat := 118140960795 + 4446974 * 2 ^ 59
def prefixEnd_4446974 : Nat := 4983230072969 + 3 ^ 40 * 4446974 * 2
def baseEnd_4446974 : Nat := 761145040015729809157915

theorem tailTrace_4446974 : CollatzResearch.WordTrace tailWord_4446974 prefixEnd_4446974 761145040015729809157915 := by
  unfold tailWord_4446974
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274308323922519442350497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108129644394253437025869317 20274308323922519442350497)
  ·
    refine ⟨15205731242941889581762873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20274308323922519442350497 15205731242941889581762873)
    ·
      refine ⟨11404298432206417186322155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15205731242941889581762873 11404298432206417186322155)
      ·
        refine ⟨17106447648309625779483233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11404298432206417186322155 17106447648309625779483233)
        ·
          refine ⟨12829835736232219334612425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17106447648309625779483233 12829835736232219334612425)
          ·
            refine ⟨9622376802174164500959319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12829835736232219334612425 9622376802174164500959319)
            ·
              refine ⟨14433565203261246751438979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622376802174164500959319 14433565203261246751438979)
              ·
                refine ⟨21650347804891870127158469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14433565203261246751438979 21650347804891870127158469)
                ·
                  refine ⟨4059440213417225648842213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21650347804891870127158469 4059440213417225648842213)
                  ·
                    refine ⟨761145040015729809157915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059440213417225648842213 761145040015729809157915)
                    ·
                      rfl

theorem cell23_4446974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4446974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446974 prefixEnd_4446974 := by exact prefixLift 4446974
  have htrace : WordTrace (prefixWord ++ tailWord_4446974) baseStart_4446974 baseEnd_4446974 := by
    simpa [prefixWord, tailWord_4446974, baseEnd_4446974] using wordTrace_append hprefix tailTrace_4446974
  have hstable : (prefixWord ++ tailWord_4446974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446974).length < 2 ^ (prefixWord ++ tailWord_4446974).sum := by decide
  have hdescent : baseEnd_4446974 < baseStart_4446974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446994 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4446994 : Nat := 118140960795 + 4446994 * 2 ^ 59
def prefixEnd_4446994 : Nat := 4983230072969 + 3 ^ 40 * 4446994 * 2
def baseEnd_4446994 : Nat := 2283445389660279349223653

theorem tailTrace_4446994 : CollatzResearch.WordTrace tailWord_4446994 prefixEnd_4446994 2283445389660279349223653 := by
  unfold tailWord_4446994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40548799012826924738633009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108130130700871799303021357 40548799012826924738633009)
  ·
    refine ⟨30411599259620193553974757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40548799012826924738633009 30411599259620193553974757)
    ·
      refine ⟨5702174861178786291370267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30411599259620193553974757 5702174861178786291370267)
      ·
        refine ⟨8553262291768179437055401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702174861178786291370267 8553262291768179437055401)
        ·
          refine ⟨6414946718826134577791551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8553262291768179437055401 6414946718826134577791551)
          ·
            refine ⟨9622420078239201866687327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414946718826134577791551 9622420078239201866687327)
            ·
              refine ⟨14433630117358802800030991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622420078239201866687327 14433630117358802800030991)
              ·
                refine ⟨21650445176038204200046487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14433630117358802800030991 21650445176038204200046487)
                ·
                  refine ⟨32475667764057306300069731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21650445176038204200046487 32475667764057306300069731)
                  ·
                    refine ⟨48713501646085959450104597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32475667764057306300069731 48713501646085959450104597)
                    ·
                      refine ⟨2283445389660279349223653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48713501646085959450104597 2283445389660279349223653)
                      ·
                        rfl

theorem cell23_4446994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4446994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4446994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4446994 prefixEnd_4446994 := by exact prefixLift 4446994
  have htrace : WordTrace (prefixWord ++ tailWord_4446994) baseStart_4446994 baseEnd_4446994 := by
    simpa [prefixWord, tailWord_4446994, baseEnd_4446994] using wordTrace_append hprefix tailTrace_4446994
  have hstable : (prefixWord ++ tailWord_4446994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446994).length < 2 ^ (prefixWord ++ tailWord_4446994).sum := by decide
  have hdescent : baseEnd_4446994 < baseStart_4446994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447021 : List Nat := [1, 5, 3, 2, 2, 1, 9]
def baseStart_4447021 : Nat := 118140960795 + 4447021 * 2 ^ 59
def prefixEnd_4447021 : Nat := 4983230072969 + 3 ^ 40 * 4447021 * 2
def baseEnd_4447021 : Nat := 28190854983184577081309

theorem tailTrace_4447021 : CollatzResearch.WordTrace tailWord_4447021 prefixEnd_4447021 28190854983184577081309 := by
  unfold tailWord_4447021
  simp only [CollatzResearch.WordTrace]
  refine ⟨162196180822209882565764917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108130787214806588377176611 162196180822209882565764917)
  ·
    refine ⟨15205891952082176490540461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162196180822209882565764917 15205891952082176490540461)
    ·
      refine ⟨5702209482030816183952673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15205891952082176490540461 5702209482030816183952673)
      ·
        refine ⟨4276657111523112137964505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5702209482030816183952673 4276657111523112137964505)
        ·
          refine ⟨3207492833642334103473379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4276657111523112137964505 3207492833642334103473379)
          ·
            refine ⟨4811239250463501155210069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207492833642334103473379 4811239250463501155210069)
            ·
              refine ⟨28190854983184577081309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4811239250463501155210069 28190854983184577081309)
              ·
                rfl

theorem cell23_4447021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 9].length) (baseStart_4447021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447021 prefixEnd_4447021 := by exact prefixLift 4447021
  have htrace : WordTrace (prefixWord ++ tailWord_4447021) baseStart_4447021 baseEnd_4447021 := by
    simpa [prefixWord, tailWord_4447021, baseEnd_4447021] using wordTrace_append hprefix tailTrace_4447021
  have hstable : (prefixWord ++ tailWord_4447021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447021).length < 2 ^ (prefixWord ++ tailWord_4447021).sum := by decide
  have hdescent : baseEnd_4447021 < baseStart_4447021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447127 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4447127 : Nat := 118140960795 + 4447127 * 2 ^ 59
def prefixEnd_4447127 : Nat := 4983230072969 + 3 ^ 40 * 4447127 * 2
def baseEnd_4447127 : Nat := 2283513682587327328860541

theorem tailTrace_4447127 : CollatzResearch.WordTrace tailWord_4447127 prefixEnd_4447127 2283513682587327328860541 := by
  unfold tailWord_4447127
  simp only [CollatzResearch.WordTrace]
  refine ⟨162200046959825862669123635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108133364639883908446082423 162200046959825862669123635)
  ·
    refine ⟨243300070439738794003685453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162200046959825862669123635 243300070439738794003685453)
    ·
      refine ⟨91237526414902047751382045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243300070439738794003685453 91237526414902047751382045)
      ·
        refine ⟨34214072405588267906768267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91237526414902047751382045 34214072405588267906768267)
        ·
          refine ⟨51321108608382401860152401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34214072405588267906768267 51321108608382401860152401)
          ·
            refine ⟨38490831456286801395114301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51321108608382401860152401 38490831456286801395114301)
            ·
              refine ⟨14434061796107550523167863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38490831456286801395114301 14434061796107550523167863)
              ·
                refine ⟨21651092694161325784751795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14434061796107550523167863 21651092694161325784751795)
                ·
                  refine ⟨32476639041241988677127693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21651092694161325784751795 32476639041241988677127693)
                  ·
                    refine ⟨12178739640465745753922885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32476639041241988677127693 12178739640465745753922885)
                    ·
                      refine ⟨2283513682587327328860541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12178739640465745753922885 2283513682587327328860541)
                      ·
                        rfl

theorem cell23_4447127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4447127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447127 prefixEnd_4447127 := by exact prefixLift 4447127
  have htrace : WordTrace (prefixWord ++ tailWord_4447127) baseStart_4447127 baseEnd_4447127 := by
    simpa [prefixWord, tailWord_4447127, baseEnd_4447127] using wordTrace_append hprefix tailTrace_4447127
  have hstable : (prefixWord ++ tailWord_4447127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447127).length < 2 ^ (prefixWord ++ tailWord_4447127).sum := by decide
  have hdescent : baseEnd_4447127 < baseStart_4447127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447157 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4447157 : Nat := 118140960795 + 4447157 * 2 ^ 59
def prefixEnd_4447157 : Nat := 4983230072969 + 3 ^ 40 * 4447157 * 2
def baseEnd_4447157 : Nat := 2283529087006962211485403

theorem tailTrace_4447157 : CollatzResearch.WordTrace tailWord_4447157 prefixEnd_4447157 2283529087006962211485403 := by
  unfold tailWord_4447157
  simp only [CollatzResearch.WordTrace]
  refine ⟨162201141149717177792715725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108134094099811451861810483 162201141149717177792715725)
  ·
    refine ⟨60825427931143941672268397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162201141149717177792715725 60825427931143941672268397)
    ·
      refine ⟨22809535474178978127100649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60825427931143941672268397 22809535474178978127100649)
      ·
        refine ⟨17107151605634233595325487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22809535474178978127100649 17107151605634233595325487)
        ·
          refine ⟨25660727408451350392988231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17107151605634233595325487 25660727408451350392988231)
          ·
            refine ⟨38491091112677025589482347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25660727408451350392988231 38491091112677025589482347)
            ·
              refine ⟨57736636669015538384223521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38491091112677025589482347 57736636669015538384223521)
              ·
                refine ⟨43302477501761653788167641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57736636669015538384223521 43302477501761653788167641)
                ·
                  refine ⟨32476858126321240341125731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43302477501761653788167641 32476858126321240341125731)
                  ·
                    refine ⟨48715287189481860511688597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32476858126321240341125731 48715287189481860511688597)
                    ·
                      refine ⟨2283529087006962211485403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48715287189481860511688597 2283529087006962211485403)
                      ·
                        rfl

theorem cell23_4447157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4447157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447157 prefixEnd_4447157 := by exact prefixLift 4447157
  have htrace : WordTrace (prefixWord ++ tailWord_4447157) baseStart_4447157 baseEnd_4447157 := by
    simpa [prefixWord, tailWord_4447157, baseEnd_4447157] using wordTrace_append hprefix tailTrace_4447157
  have hstable : (prefixWord ++ tailWord_4447157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447157).length < 2 ^ (prefixWord ++ tailWord_4447157).sum := by decide
  have hdescent : baseEnd_4447157 < baseStart_4447157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447188 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4447188 : Nat := 118140960795 + 4447188 * 2 ^ 59
def prefixEnd_4447188 : Nat := 4983230072969 + 3 ^ 40 * 4447188 * 2
def baseEnd_4447188 : Nat := 761181668302417196732587

theorem tailTrace_4447188 : CollatzResearch.WordTrace tailWord_4447188 prefixEnd_4447188 761181668302417196732587 := by
  unfold tailWord_4447188
  simp only [CollatzResearch.WordTrace]
  refine ⟨81101135906302435043547109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108134847875069913391396145 81101135906302435043547109)
  ·
    refine ⟨15206462982431706570665083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81101135906302435043547109 15206462982431706570665083)
    ·
      refine ⟨22809694473647559855997625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15206462982431706570665083 22809694473647559855997625)
      ·
        refine ⟨17107270855235669891998219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22809694473647559855997625 17107270855235669891998219)
        ·
          refine ⟨25660906282853504837997329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17107270855235669891998219 25660906282853504837997329)
          ·
            refine ⟨19245679712140128628497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25660906282853504837997329 19245679712140128628497997)
            ·
              refine ⟨7217129892052548235686749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19245679712140128628497997 7217129892052548235686749)
              ·
                refine ⟨2706423709519705588382531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7217129892052548235686749 2706423709519705588382531)
                ·
                  refine ⟨4059635564279558382573797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706423709519705588382531 4059635564279558382573797)
                  ·
                    refine ⟨761181668302417196732587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059635564279558382573797 761181668302417196732587)
                    ·
                      rfl

theorem cell23_4447188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4447188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447188 prefixEnd_4447188 := by exact prefixLift 4447188
  have htrace : WordTrace (prefixWord ++ tailWord_4447188) baseStart_4447188 baseEnd_4447188 := by
    simpa [prefixWord, tailWord_4447188, baseEnd_4447188] using wordTrace_append hprefix tailTrace_4447188
  have hstable : (prefixWord ++ tailWord_4447188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447188).length < 2 ^ (prefixWord ++ tailWord_4447188).sum := by decide
  have hdescent : baseEnd_4447188 < baseStart_4447188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447204 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_4447204 : Nat := 118140960795 + 4447204 * 2 ^ 59
def prefixEnd_4447204 : Nat := 4983230072969 + 3 ^ 40 * 4447204 * 2
def baseEnd_4447204 : Nat := 2283553220597723527597687

theorem tailTrace_4447204 : CollatzResearch.WordTrace tailWord_4447204 prefixEnd_4447204 2283553220597723527597687 := by
  unfold tailWord_4447204
  simp only [CollatzResearch.WordTrace]
  refine ⟨81101427690273452409838333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108135236920364603213117777 81101427690273452409838333)
  ·
    refine ⟨30413035383852544653689375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81101427690273452409838333 30413035383852544653689375)
    ·
      refine ⟨45619553075778816980534063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30413035383852544653689375 45619553075778816980534063)
      ·
        refine ⟨68429329613668225470801095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45619553075778816980534063 68429329613668225470801095)
        ·
          refine ⟨102643994420502338206201643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68429329613668225470801095 102643994420502338206201643)
          ·
            refine ⟨153965991630753507309302465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102643994420502338206201643 153965991630753507309302465)
            ·
              refine ⟨115474493723065130481976849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153965991630753507309302465 115474493723065130481976849)
              ·
                refine ⟨86605870292298847861482637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115474493723065130481976849 86605870292298847861482637)
                ·
                  refine ⟨32477201359612067948055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86605870292298847861482637 32477201359612067948055989)
                  ·
                    refine ⟨3044737627463631370130249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32477201359612067948055989 3044737627463631370130249)
                    ·
                      refine ⟨2283553220597723527597687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044737627463631370130249 2283553220597723527597687)
                      ·
                        rfl

theorem cell23_4447204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_4447204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447204 prefixEnd_4447204 := by exact prefixLift 4447204
  have htrace : WordTrace (prefixWord ++ tailWord_4447204) baseStart_4447204 baseEnd_4447204 := by
    simpa [prefixWord, tailWord_4447204, baseEnd_4447204] using wordTrace_append hprefix tailTrace_4447204
  have hstable : (prefixWord ++ tailWord_4447204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447204).length < 2 ^ (prefixWord ++ tailWord_4447204).sum := by decide
  have hdescent : baseEnd_4447204 < baseStart_4447204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447205 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_4447205 : Nat := 118140960795 + 4447205 * 2 ^ 59
def prefixEnd_4447205 : Nat := 4983230072969 + 3 ^ 40 * 4447205 * 2
def baseEnd_4447205 : Nat := 761184578026126007895061

theorem tailTrace_4447205 : CollatzResearch.WordTrace tailWord_4447205 prefixEnd_4447205 761184578026126007895061 := by
  unfold tailWord_4447205
  simp only [CollatzResearch.WordTrace]
  refine ⟨162202891853543281990463069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108135261235695521326975379 162202891853543281990463069)
  ·
    refine ⟨60826084445078730746423651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162202891853543281990463069 60826084445078730746423651)
    ·
      refine ⟨91239126667618096119635477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60826084445078730746423651 91239126667618096119635477)
      ·
        refine ⟨4276834062544598255607913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91239126667618096119635477 4276834062544598255607913)
        ·
          refine ⟨3207625546908448691705935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4276834062544598255607913 3207625546908448691705935)
          ·
            refine ⟨4811438320362673037558903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207625546908448691705935 4811438320362673037558903)
            ·
              refine ⟨7217157480544009556338355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811438320362673037558903 7217157480544009556338355)
              ·
                refine ⟨10825736220816014334507533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217157480544009556338355 10825736220816014334507533)
                ·
                  refine ⟨4059651082806005375440325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10825736220816014334507533 4059651082806005375440325)
                  ·
                    refine ⟨761184578026126007895061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059651082806005375440325 761184578026126007895061)
                    ·
                      rfl

theorem cell23_4447205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_4447205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447205 prefixEnd_4447205 := by exact prefixLift 4447205
  have htrace : WordTrace (prefixWord ++ tailWord_4447205) baseStart_4447205 baseEnd_4447205 := by
    simpa [prefixWord, tailWord_4447205, baseEnd_4447205] using wordTrace_append hprefix tailTrace_4447205
  have hstable : (prefixWord ++ tailWord_4447205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447205).length < 2 ^ (prefixWord ++ tailWord_4447205).sum := by decide
  have hdescent : baseEnd_4447205 < baseStart_4447205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447227 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 6]
def baseStart_4447227 : Nat := 118140960795 + 4447227 * 2 ^ 59
def prefixEnd_4447227 : Nat := 4983230072969 + 3 ^ 40 * 4447227 * 2
def baseEnd_4447227 : Nat := 761188343550925645870027

theorem tailTrace_4447227 : CollatzResearch.WordTrace tailWord_4447227 prefixEnd_4447227 761188343550925645870027 := by
  unfold tailWord_4447227
  simp only [CollatzResearch.WordTrace]
  refine ⟨162203694259463579747763935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108135796172975719831842623 162203694259463579747763935)
  ·
    refine ⟨243305541389195369621645903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162203694259463579747763935 243305541389195369621645903)
    ·
      refine ⟨364958312083793054432468855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243305541389195369621645903 364958312083793054432468855)
      ·
        refine ⟨547437468125689581648703283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364958312083793054432468855 547437468125689581648703283)
        ·
          refine ⟨821156202188534372473054925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547437468125689581648703283 821156202188534372473054925)
          ·
            refine ⟨307933575820700389677395597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821156202188534372473054925 307933575820700389677395597)
            ·
              refine ⟨115475090932762646129023349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307933575820700389677395597 115475090932762646129023349)
              ·
                refine ⟨10825789774946498074595939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115475090932762646129023349 10825789774946498074595939)
                ·
                  refine ⟨16238684662419747111893909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10825789774946498074595939 16238684662419747111893909)
                  ·
                    refine ⟨761188343550925645870027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16238684662419747111893909 761188343550925645870027)
                    ·
                      rfl

theorem cell23_4447227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_4447227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447227 prefixEnd_4447227 := by exact prefixLift 4447227
  have htrace : WordTrace (prefixWord ++ tailWord_4447227) baseStart_4447227 baseEnd_4447227 := by
    simpa [prefixWord, tailWord_4447227, baseEnd_4447227] using wordTrace_append hprefix tailTrace_4447227
  have hstable : (prefixWord ++ tailWord_4447227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447227).length < 2 ^ (prefixWord ++ tailWord_4447227).sum := by decide
  have hdescent : baseEnd_4447227 < baseStart_4447227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447244 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_4447244 : Nat := 118140960795 + 4447244 * 2 ^ 59
def prefixEnd_4447244 : Nat := 4983230072969 + 3 ^ 40 * 4447244 * 2
def baseEnd_4447244 : Nat := 761191253274634457032501

theorem tailTrace_4447244 : CollatzResearch.WordTrace tailWord_4447244 prefixEnd_4447244 761191253274634457032501 := by
  unfold tailWord_4447244
  simp only [CollatzResearch.WordTrace]
  refine ⟨81102157150200995825566393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108136209533601327767421857 81102157150200995825566393)
  ·
    refine ⟨60826617862650746869174795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81102157150200995825566393 60826617862650746869174795)
    ·
      refine ⟨91239926793976120303762193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60826617862650746869174795 91239926793976120303762193)
      ·
        refine ⟨68429945095482090227821645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91239926793976120303762193 68429945095482090227821645)
        ·
          refine ⟨25661229410805783835433117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68429945095482090227821645 25661229410805783835433117)
          ·
            refine ⟨9622961029052168938287419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25661229410805783835433117 9622961029052168938287419)
            ·
              refine ⟨14434441543578253407431129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622961029052168938287419 14434441543578253407431129)
              ·
                refine ⟨10825831157683690055573347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14434441543578253407431129 10825831157683690055573347)
                ·
                  refine ⟨16238746736525535083360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10825831157683690055573347 16238746736525535083360021)
                  ·
                    refine ⟨761191253274634457032501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16238746736525535083360021 761191253274634457032501)
                    ·
                      rfl

theorem cell23_4447244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_4447244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447244 prefixEnd_4447244 := by exact prefixLift 4447244
  have htrace : WordTrace (prefixWord ++ tailWord_4447244) baseStart_4447244 baseEnd_4447244 := by
    simpa [prefixWord, tailWord_4447244, baseEnd_4447244] using wordTrace_append hprefix tailTrace_4447244
  have hstable : (prefixWord ++ tailWord_4447244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447244).length < 2 ^ (prefixWord ++ tailWord_4447244).sum := by decide
  have hdescent : baseEnd_4447244 < baseStart_4447244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447287 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 7]
def baseStart_4447287 : Nat := 118140960795 + 4447287 * 2 ^ 59
def prefixEnd_4447287 : Nat := 4983230072969 + 3 ^ 40 * 4447287 * 2
def baseEnd_4447287 : Nat := 761198613164015567619935

theorem tailTrace_4447287 : CollatzResearch.WordTrace tailWord_4447287 prefixEnd_4447287 761198613164015567619935 := by
  unfold tailWord_4447287
  simp only [CollatzResearch.WordTrace]
  refine ⟨162205882639246209994948115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108137255092830806663298743 162205882639246209994948115)
  ·
    refine ⟨243308823958869314992422173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162205882639246209994948115 243308823958869314992422173)
    ·
      refine ⟨91240808984575993122158315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243308823958869314992422173 91240808984575993122158315)
      ·
        refine ⟨136861213476863989683237473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91240808984575993122158315 136861213476863989683237473)
        ·
          refine ⟨102645910107647992262428105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136861213476863989683237473 102645910107647992262428105)
          ·
            refine ⟨76984432580735994196821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102645910107647992262428105 76984432580735994196821079)
            ·
              refine ⟨115476648871103991295231619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76984432580735994196821079 115476648871103991295231619)
              ·
                refine ⟨173214973306655986942847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115476648871103991295231619 173214973306655986942847429)
                ·
                  refine ⟨32477807494997997551783893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173214973306655986942847429 32477807494997997551783893)
                  ·
                    refine ⟨761198613164015567619935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32477807494997997551783893 761198613164015567619935)
                    ·
                      rfl

theorem cell23_4447287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_4447287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447287 prefixEnd_4447287 := by exact prefixLift 4447287
  have htrace : WordTrace (prefixWord ++ tailWord_4447287) baseStart_4447287 baseEnd_4447287 := by
    simpa [prefixWord, tailWord_4447287, baseEnd_4447287] using wordTrace_append hprefix tailTrace_4447287
  have hstable : (prefixWord ++ tailWord_4447287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447287).length < 2 ^ (prefixWord ++ tailWord_4447287).sum := by decide
  have hdescent : baseEnd_4447287 < baseStart_4447287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447302 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4447302 : Nat := 118140960795 + 4447302 * 2 ^ 59
def prefixEnd_4447302 : Nat := 4983230072969 + 3 ^ 40 * 4447302 * 2
def baseEnd_4447302 : Nat := 2283603541701864144172237

theorem tailTrace_4447302 : CollatzResearch.WordTrace tailWord_4447302 prefixEnd_4447302 2283603541701864144172237 := by
  unfold tailWord_4447302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068950929193495861148255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108137619822794578371162773 5068950929193495861148255)
  ·
    refine ⟨7603426393790243791722383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5068950929193495861148255 7603426393790243791722383)
    ·
      refine ⟨11405139590685365687583575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7603426393790243791722383 11405139590685365687583575)
      ·
        refine ⟨17107709386028048531375363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11405139590685365687583575 17107709386028048531375363)
        ·
          refine ⟨25661564079042072797063045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17107709386028048531375363 25661564079042072797063045)
          ·
            refine ⟨4811543264820388649449321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25661564079042072797063045 4811543264820388649449321)
            ·
              refine ⟨3608657448615291487086991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4811543264820388649449321 3608657448615291487086991)
              ·
                refine ⟨5412986172922937230630487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608657448615291487086991 5412986172922937230630487)
                ·
                  refine ⟨8119479259384405845945731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412986172922937230630487 8119479259384405845945731)
                  ·
                    refine ⟨12179218889076608768918597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8119479259384405845945731 12179218889076608768918597)
                    ·
                      refine ⟨2283603541701864144172237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12179218889076608768918597 2283603541701864144172237)
                      ·
                        rfl

theorem cell23_4447302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4447302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447302 prefixEnd_4447302 := by exact prefixLift 4447302
  have htrace : WordTrace (prefixWord ++ tailWord_4447302) baseStart_4447302 baseEnd_4447302 := by
    simpa [prefixWord, tailWord_4447302, baseEnd_4447302] using wordTrace_append hprefix tailTrace_4447302
  have hstable : (prefixWord ++ tailWord_4447302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447302).length < 2 ^ (prefixWord ++ tailWord_4447302).sum := by decide
  have hdescent : baseEnd_4447302 < baseStart_4447302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447335 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_4447335 : Nat := 118140960795 + 4447335 * 2 ^ 59
def prefixEnd_4447335 : Nat := 4983230072969 + 3 ^ 40 * 4447335 * 2
def baseEnd_4447335 : Nat := 2283620486563462515059585

theorem tailTrace_4447335 : CollatzResearch.WordTrace tailWord_4447335 prefixEnd_4447335 2283620486563462515059585 := by
  unfold tailWord_4447335
  simp only [CollatzResearch.WordTrace]
  refine ⟨162207633343072314192695459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108138422228714876128463639 162207633343072314192695459)
  ·
    refine ⟨243311450014608471289043189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162207633343072314192695459 243311450014608471289043189)
    ·
      refine ⟨22810448438869544183347799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 243311450014608471289043189 22810448438869544183347799)
      ·
        refine ⟨34215672658304316275021699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22810448438869544183347799 34215672658304316275021699)
        ·
          refine ⟨51323508987456474412532549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34215672658304316275021699 51323508987456474412532549)
          ·
            refine ⟨9623157935148088952349853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51323508987456474412532549 9623157935148088952349853)
            ·
              refine ⟨3608684225680533357131195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9623157935148088952349853 3608684225680533357131195)
              ·
                refine ⟨5413026338520800035696793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608684225680533357131195 5413026338520800035696793)
                ·
                  refine ⟨4059769753890600026772595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413026338520800035696793 4059769753890600026772595)
                  ·
                    refine ⟨6089654630835900040158893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059769753890600026772595 6089654630835900040158893)
                    ·
                      refine ⟨2283620486563462515059585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6089654630835900040158893 2283620486563462515059585)
                      ·
                        rfl

theorem cell23_4447335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_4447335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447335 prefixEnd_4447335 := by exact prefixLift 4447335
  have htrace : WordTrace (prefixWord ++ tailWord_4447335) baseStart_4447335 baseEnd_4447335 := by
    simpa [prefixWord, tailWord_4447335, baseEnd_4447335] using wordTrace_append hprefix tailTrace_4447335
  have hstable : (prefixWord ++ tailWord_4447335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447335).length < 2 ^ (prefixWord ++ tailWord_4447335).sum := by decide
  have hdescent : baseEnd_4447335 < baseStart_4447335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447344 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_4447344 : Nat := 118140960795 + 4447344 * 2 ^ 59
def prefixEnd_4447344 : Nat := 4983230072969 + 3 ^ 40 * 4447344 * 2
def baseEnd_4447344 : Nat := 2283625107889352979847043

theorem tailTrace_4447344 : CollatzResearch.WordTrace tailWord_4447344 prefixEnd_4447344 2283625107889352979847043 := by
  unfold tailWord_4447344
  simp only [CollatzResearch.WordTrace]
  refine ⟨81103980800019854364886543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108138641066693139153182057 81103980800019854364886543)
  ·
    refine ⟨121655971200029781547329815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81103980800019854364886543 121655971200029781547329815)
    ·
      refine ⟨182483956800044672320994723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121655971200029781547329815 182483956800044672320994723)
      ·
        refine ⟨273725935200067008481492085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182483956800044672320994723 273725935200067008481492085)
        ·
          refine ⟨25661806425006282045139883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 273725935200067008481492085 25661806425006282045139883)
          ·
            refine ⟨38492709637509423067709825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25661806425006282045139883 38492709637509423067709825)
            ·
              refine ⟨28869532228132067300782369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38492709637509423067709825 28869532228132067300782369)
              ·
                refine ⟨21652149171099050475586777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28869532228132067300782369 21652149171099050475586777)
                ·
                  refine ⟨16239111878324287856690083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21652149171099050475586777 16239111878324287856690083)
                  ·
                    refine ⟨24358667817486431785035125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16239111878324287856690083 24358667817486431785035125)
                    ·
                      refine ⟨2283625107889352979847043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24358667817486431785035125 2283625107889352979847043)
                      ·
                        rfl

theorem cell23_4447344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_4447344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447344 prefixEnd_4447344 := by exact prefixLift 4447344
  have htrace : WordTrace (prefixWord ++ tailWord_4447344) baseStart_4447344 baseEnd_4447344 := by
    simpa [prefixWord, tailWord_4447344, baseEnd_4447344] using wordTrace_append hprefix tailTrace_4447344
  have hstable : (prefixWord ++ tailWord_4447344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447344).length < 2 ^ (prefixWord ++ tailWord_4447344).sum := by decide
  have hdescent : baseEnd_4447344 < baseStart_4447344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447361 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4447361 : Nat := 118140960795 + 4447361 * 2 ^ 59
def prefixEnd_4447361 : Nat := 4983230072969 + 3 ^ 40 * 4447361 * 2
def baseEnd_4447361 : Nat := 2283633837060479413334465

theorem tailTrace_4447361 : CollatzResearch.WordTrace tailWord_4447361 prefixEnd_4447361 2283633837060479413334465 := by
  unfold tailWord_4447361
  simp only [CollatzResearch.WordTrace]
  refine ⟨162208581640978120633141937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108139054427318747088761291 162208581640978120633141937)
  ·
    refine ⟨121656436230733590474856453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162208581640978120633141937 121656436230733590474856453)
    ·
      refine ⟨22810581793262548214035585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121656436230733590474856453 22810581793262548214035585)
      ·
        refine ⟨17107936344946911160526689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22810581793262548214035585 17107936344946911160526689)
        ·
          refine ⟨12830952258710183370395017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17107936344946911160526689 12830952258710183370395017)
          ·
            refine ⟨9623214194032637527796263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12830952258710183370395017 9623214194032637527796263)
            ·
              refine ⟨14434821291048956291694395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623214194032637527796263 14434821291048956291694395)
              ·
                refine ⟨21652231936573434437541593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14434821291048956291694395 21652231936573434437541593)
                ·
                  refine ⟨16239173952430075828156195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21652231936573434437541593 16239173952430075828156195)
                  ·
                    refine ⟨24358760928645113742234293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16239173952430075828156195 24358760928645113742234293)
                    ·
                      refine ⟨2283633837060479413334465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24358760928645113742234293 2283633837060479413334465)
                      ·
                        rfl

theorem cell23_4447361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4447361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447361 prefixEnd_4447361 := by exact prefixLift 4447361
  have htrace : WordTrace (prefixWord ++ tailWord_4447361) baseStart_4447361 baseEnd_4447361 := by
    simpa [prefixWord, tailWord_4447361, baseEnd_4447361] using wordTrace_append hprefix tailTrace_4447361
  have hstable : (prefixWord ++ tailWord_4447361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447361).length < 2 ^ (prefixWord ++ tailWord_4447361).sum := by decide
  have hdescent : baseEnd_4447361 < baseStart_4447361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447426 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4447426 : Nat := 118140960795 + 4447426 * 2 ^ 59
def prefixEnd_4447426 : Nat := 4983230072969 + 3 ^ 40 * 4447426 * 2
def baseEnd_4447426 : Nat := 2283667213303021659021667

theorem tailTrace_4447426 : CollatzResearch.WordTrace tailWord_4447426 prefixEnd_4447426 2283667213303021659021667 := by
  unfold tailWord_4447426
  simp only [CollatzResearch.WordTrace]
  refine ⟨40552738096435659183564533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108140634923828424489505421 40552738096435659183564533)
  ·
    refine ⟨3801819196540843048459175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40552738096435659183564533 3801819196540843048459175)
    ·
      refine ⟨5702728794811264572688763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801819196540843048459175 5702728794811264572688763)
      ·
        refine ⟨8554093192216896859033145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702728794811264572688763 8554093192216896859033145)
        ·
          refine ⟨6415569894162672644274859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8554093192216896859033145 6415569894162672644274859)
          ·
            refine ⟨9623354841244008966412289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415569894162672644274859 9623354841244008966412289)
            ·
              refine ⟨7217516130933006724809217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9623354841244008966412289 7217516130933006724809217)
              ·
                refine ⟨5413137098199755043606913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217516130933006724809217 5413137098199755043606913)
                ·
                  refine ⟨4059852823649816282705185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413137098199755043606913 4059852823649816282705185)
                  ·
                    refine ⟨3044889617737362212028889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4059852823649816282705185 3044889617737362212028889)
                    ·
                      refine ⟨2283667213303021659021667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044889617737362212028889 2283667213303021659021667)
                      ·
                        rfl

theorem cell23_4447426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4447426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447426 prefixEnd_4447426 := by exact prefixLift 4447426
  have htrace : WordTrace (prefixWord ++ tailWord_4447426) baseStart_4447426 baseEnd_4447426 := by
    simpa [prefixWord, tailWord_4447426, baseEnd_4447426] using wordTrace_append hprefix tailTrace_4447426
  have hstable : (prefixWord ++ tailWord_4447426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447426).length < 2 ^ (prefixWord ++ tailWord_4447426).sum := by decide
  have hdescent : baseEnd_4447426 < baseStart_4447426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447431 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_4447431 : Nat := 118140960795 + 4447431 * 2 ^ 59
def prefixEnd_4447431 : Nat := 4983230072969 + 3 ^ 40 * 4447431 * 2
def baseEnd_4447431 : Nat := 2283669780706294139459143

theorem tailTrace_4447431 : CollatzResearch.WordTrace tailWord_4447431 prefixEnd_4447431 2283669780706294139459143 := by
  unfold tailWord_4447431
  simp only [CollatzResearch.WordTrace]
  refine ⟨162211134750724522588190147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108140756500483015058793431 162211134750724522588190147)
  ·
    refine ⟨243316702126086783882285221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162211134750724522588190147 243316702126086783882285221)
    ·
      refine ⟨45621881648641271977928479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243316702126086783882285221 45621881648641271977928479)
      ·
        refine ⟨68432822472961907966892719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45621881648641271977928479 68432822472961907966892719)
        ·
          refine ⟨102649233709442861950339079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68432822472961907966892719 102649233709442861950339079)
          ·
            refine ⟨153973850564164292925508619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102649233709442861950339079 153973850564164292925508619)
            ·
              refine ⟨230960775846246439388262929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153973850564164292925508619 230960775846246439388262929)
              ·
                refine ⟨173220581884684829541197197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230960775846246439388262929 173220581884684829541197197)
                ·
                  refine ⟨64957718206756811077948949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173220581884684829541197197 64957718206756811077948949)
                  ·
                    refine ⟨3044893040941725519278857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64957718206756811077948949 3044893040941725519278857)
                    ·
                      refine ⟨2283669780706294139459143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3044893040941725519278857 2283669780706294139459143)
                      ·
                        rfl

theorem cell23_4447431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_4447431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447431 prefixEnd_4447431 := by exact prefixLift 4447431
  have htrace : WordTrace (prefixWord ++ tailWord_4447431) baseStart_4447431 baseEnd_4447431 := by
    simpa [prefixWord, tailWord_4447431, baseEnd_4447431] using wordTrace_append hprefix tailTrace_4447431
  have hstable : (prefixWord ++ tailWord_4447431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447431).length < 2 ^ (prefixWord ++ tailWord_4447431).sum := by decide
  have hdescent : baseEnd_4447431 < baseStart_4447431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447441 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_4447441 : Nat := 118140960795 + 4447441 * 2 ^ 59
def prefixEnd_4447441 : Nat := 4983230072969 + 3 ^ 40 * 4447441 * 2
def baseEnd_4447441 : Nat := 761224971837613033444699

theorem tailTrace_4447441 : CollatzResearch.WordTrace tailWord_4447441 prefixEnd_4447441 761224971837613033444699 := by
  unfold tailWord_4447441
  simp only [CollatzResearch.WordTrace]
  refine ⟨162211499480688294296054177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108140999653792196197369451 162211499480688294296054177)
  ·
    refine ⟨121658624610516220722040633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162211499480688294296054177 121658624610516220722040633)
    ·
      refine ⟨91243968457887165541530475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121658624610516220722040633 91243968457887165541530475)
      ·
        refine ⟨136865952686830748312295713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91243968457887165541530475 136865952686830748312295713)
        ·
          refine ⟨102649464515123061234221785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136865952686830748312295713 102649464515123061234221785)
          ·
            refine ⟨76987098386342295925666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102649464515123061234221785 76987098386342295925666339)
            ·
              refine ⟨115480647579513443888499509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76987098386342295925666339 115480647579513443888499509)
              ·
                refine ⟨10826310710579385364546829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115480647579513443888499509 10826310710579385364546829)
                ·
                  refine ⟨4059866516467269511705061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10826310710579385364546829 4059866516467269511705061)
                  ·
                    refine ⟨761224971837613033444699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059866516467269511705061 761224971837613033444699)
                    ·
                      rfl

theorem cell23_4447441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_4447441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447441 prefixEnd_4447441 := by exact prefixLift 4447441
  have htrace : WordTrace (prefixWord ++ tailWord_4447441) baseStart_4447441 baseEnd_4447441 := by
    simpa [prefixWord, tailWord_4447441, baseEnd_4447441] using wordTrace_append hprefix tailTrace_4447441
  have hstable : (prefixWord ++ tailWord_4447441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447441).length < 2 ^ (prefixWord ++ tailWord_4447441).sum := by decide
  have hdescent : baseEnd_4447441 < baseStart_4447441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447468 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_4447468 : Nat := 118140960795 + 4447468 * 2 ^ 59
def prefixEnd_4447468 : Nat := 4983230072969 + 3 ^ 40 * 4447468 * 2
def baseEnd_4447468 : Nat := 2283688779490510494696473

theorem tailTrace_4447468 : CollatzResearch.WordTrace tailWord_4447468 prefixEnd_4447468 2283688779490510494696473 := by
  unfold tailWord_4447468
  simp only [CollatzResearch.WordTrace]
  refine ⟨81106242125795238953643529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108141656167726985271524705 81106242125795238953643529)
  ·
    refine ⟨60829681594346429215232647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81106242125795238953643529 60829681594346429215232647)
    ·
      refine ⟨91244522391519643822848971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60829681594346429215232647 91244522391519643822848971)
      ·
        refine ⟨136866783587279465734273457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91244522391519643822848971 136866783587279465734273457)
        ·
          refine ⟨102650087690459599300705093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136866783587279465734273457 102650087690459599300705093)
          ·
            refine ⟨19246891441961174868882205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102650087690459599300705093 19246891441961174868882205)
            ·
              refine ⟨7217584290735440575830827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19246891441961174868882205 7217584290735440575830827)
              ·
                refine ⟨10826376436103160863746241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217584290735440575830827 10826376436103160863746241)
                ·
                  refine ⟨8119782327077370647809681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10826376436103160863746241 8119782327077370647809681)
                  ·
                    refine ⟨6089836745308027985857261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8119782327077370647809681 6089836745308027985857261)
                    ·
                      refine ⟨2283688779490510494696473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6089836745308027985857261 2283688779490510494696473)
                      ·
                        rfl

theorem cell23_4447468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_4447468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447468 prefixEnd_4447468 := by exact prefixLift 4447468
  have htrace : WordTrace (prefixWord ++ tailWord_4447468) baseStart_4447468 baseEnd_4447468 := by
    simpa [prefixWord, tailWord_4447468, baseEnd_4447468] using wordTrace_append hprefix tailTrace_4447468
  have hstable : (prefixWord ++ tailWord_4447468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447468).length < 2 ^ (prefixWord ++ tailWord_4447468).sum := by decide
  have hdescent : baseEnd_4447468 < baseStart_4447468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447475 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 1, 4]
def baseStart_4447475 : Nat := 118140960795 + 4447475 * 2 ^ 59
def prefixEnd_4447475 : Nat := 4983230072969 + 3 ^ 40 * 4447475 * 2
def baseEnd_4447475 : Nat := 761230791285030655769647

theorem tailTrace_4447475 : CollatzResearch.WordTrace tailWord_4447475 prefixEnd_4447475 761230791285030655769647 := by
  unfold tailWord_4447475
  simp only [CollatzResearch.WordTrace]
  refine ⟨162212739562565118102791879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108141826375043412068527919 162212739562565118102791879)
  ·
    refine ⟨243319109343847677154187819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162212739562565118102791879 243319109343847677154187819)
    ·
      refine ⟨364978664015771515731281729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243319109343847677154187819 364978664015771515731281729)
      ·
        refine ⟨273733998011828636798461297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364978664015771515731281729 273733998011828636798461297)
        ·
          refine ⟨205300498508871477598845973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273733998011828636798461297 205300498508871477598845973)
          ·
            refine ⟨9623460867603350512445905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205300498508871477598845973 9623460867603350512445905)
            ·
              refine ⟨7217595650702512884334429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9623460867603350512445905 7217595650702512884334429)
              ·
                refine ⟨2706598369013442331625411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7217595650702512884334429 2706598369013442331625411)
                ·
                  refine ⟨4059897553520163497438117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706598369013442331625411 4059897553520163497438117)
                  ·
                    refine ⟨761230791285030655769647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059897553520163497438117 761230791285030655769647)
                    ·
                      rfl

theorem cell23_4447475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 4].length) (baseStart_4447475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447475 prefixEnd_4447475 := by exact prefixLift 4447475
  have htrace : WordTrace (prefixWord ++ tailWord_4447475) baseStart_4447475 baseEnd_4447475 := by
    simpa [prefixWord, tailWord_4447475, baseEnd_4447475] using wordTrace_append hprefix tailTrace_4447475
  have hstable : (prefixWord ++ tailWord_4447475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447475).length < 2 ^ (prefixWord ++ tailWord_4447475).sum := by decide
  have hdescent : baseEnd_4447475 < baseStart_4447475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447548 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_4447548 : Nat := 118140960795 + 4447548 * 2 ^ 59
def prefixEnd_4447548 : Nat := 4983230072969 + 3 ^ 40 * 4447548 * 2
def baseEnd_4447548 : Nat := 761243285980956727232035

theorem tailTrace_4447548 : CollatzResearch.WordTrace tailWord_4447548 prefixEnd_4447548 761243285980956727232035 := by
  unfold tailWord_4447548
  simp only [CollatzResearch.WordTrace]
  refine ⟨81107701045650325785099649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108143601394200434380132865 81107701045650325785099649)
  ·
    refine ⟨60830775784237744338824737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81107701045650325785099649 60830775784237744338824737)
    ·
      refine ⟨45623081838178308254118553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60830775784237744338824737 45623081838178308254118553)
      ·
        refine ⟨34217311378633731190588915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45623081838178308254118553 34217311378633731190588915)
        ·
          refine ⟨51325967067950596785883373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34217311378633731190588915 51325967067950596785883373)
          ·
            refine ⟨19247237650481473794706265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51325967067950596785883373 19247237650481473794706265)
            ·
              refine ⟨14435428237861105346029699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19247237650481473794706265 14435428237861105346029699)
              ·
                refine ⟨21653142356791658019044549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14435428237861105346029699 21653142356791658019044549)
                ·
                  refine ⟨4059964191898435878570853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21653142356791658019044549 4059964191898435878570853)
                  ·
                    refine ⟨761243285980956727232035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059964191898435878570853 761243285980956727232035)
                    ·
                      rfl

theorem cell23_4447548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_4447548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447548 prefixEnd_4447548 := by exact prefixLift 4447548
  have htrace : WordTrace (prefixWord ++ tailWord_4447548) baseStart_4447548 baseEnd_4447548 := by
    simpa [prefixWord, tailWord_4447548, baseEnd_4447548] using wordTrace_append hprefix tailTrace_4447548
  have hstable : (prefixWord ++ tailWord_4447548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447548).length < 2 ^ (prefixWord ++ tailWord_4447548).sum := by decide
  have hdescent : baseEnd_4447548 < baseStart_4447548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447549 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4447549 : Nat := 118140960795 + 4447549 * 2 ^ 59
def prefixEnd_4447549 : Nat := 4983230072969 + 3 ^ 40 * 4447549 * 2
def baseEnd_4447549 : Nat := 2283730371423524677783601

theorem tailTrace_4447549 : CollatzResearch.WordTrace tailWord_4447549 prefixEnd_4447549 2283730371423524677783601 := by
  unfold tailWord_4447549
  simp only [CollatzResearch.WordTrace]
  refine ⟨162215438564297028740985701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108143625709531352493990467 162215438564297028740985701)
  ·
    refine ⟨30415394730805692888934819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162215438564297028740985701 30415394730805692888934819)
    ·
      refine ⟨45623092096208539333402229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30415394730805692888934819 45623092096208539333402229)
      ·
        refine ⟨4277164884019550562506459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45623092096208539333402229 4277164884019550562506459)
        ·
          refine ⟨6415747326029325843759689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277164884019550562506459 6415747326029325843759689)
          ·
            refine ⟨4811810494521994382819767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6415747326029325843759689 4811810494521994382819767)
            ·
              refine ⟨7217715741782991574229651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811810494521994382819767 7217715741782991574229651)
              ·
                refine ⟨10826573612674487361344477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217715741782991574229651 10826573612674487361344477)
                ·
                  refine ⟨4059965104752932760504179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10826573612674487361344477 4059965104752932760504179)
                  ·
                    refine ⟨6089947657129399140756269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059965104752932760504179 6089947657129399140756269)
                    ·
                      refine ⟨2283730371423524677783601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6089947657129399140756269 2283730371423524677783601)
                      ·
                        rfl

theorem cell23_4447549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4447549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447549 prefixEnd_4447549 := by exact prefixLift 4447549
  have htrace : WordTrace (prefixWord ++ tailWord_4447549) baseStart_4447549 baseEnd_4447549 := by
    simpa [prefixWord, tailWord_4447549, baseEnd_4447549] using wordTrace_append hprefix tailTrace_4447549
  have hstable : (prefixWord ++ tailWord_4447549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447549).length < 2 ^ (prefixWord ++ tailWord_4447549).sum := by decide
  have hdescent : baseEnd_4447549 < baseStart_4447549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447551 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_4447551 : Nat := 118140960795 + 4447551 * 2 ^ 59
def prefixEnd_4447551 : Nat := 4983230072969 + 3 ^ 40 * 4447551 * 2
def baseEnd_4447551 : Nat := 2283731398384833669958591

theorem tailTrace_4447551 : CollatzResearch.WordTrace tailWord_4447551 prefixEnd_4447551 2283731398384833669958591 := by
  unfold tailWord_4447551
  simp only [CollatzResearch.WordTrace]
  refine ⟨162215511510289783082558507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108143674340193188721705671 162215511510289783082558507)
  ·
    refine ⟨243323267265434674623837761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162215511510289783082558507 243323267265434674623837761)
    ·
      refine ⟨182492450449076005967878321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243323267265434674623837761 182492450449076005967878321)
      ·
        refine ⟨136869337836807004475908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182492450449076005967878321 136869337836807004475908741)
        ·
          refine ⟨25663000844401313339232889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136869337836807004475908741 25663000844401313339232889)
          ·
            refine ⟨19247250633300985004424667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25663000844401313339232889 19247250633300985004424667)
            ·
              refine ⟨28870875949951477506637001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19247250633300985004424667 28870875949951477506637001)
              ·
                refine ⟨21653156962463608129977751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28870875949951477506637001 21653156962463608129977751)
                ·
                  refine ⟨32479735443695412194966627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21653156962463608129977751 32479735443695412194966627)
                  ·
                    refine ⟨48719603165543118292449941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32479735443695412194966627 48719603165543118292449941)
                    ·
                      refine ⟨2283731398384833669958591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48719603165543118292449941 2283731398384833669958591)
                      ·
                        rfl

theorem cell23_4447551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_4447551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447551 prefixEnd_4447551 := by exact prefixLift 4447551
  have htrace : WordTrace (prefixWord ++ tailWord_4447551) baseStart_4447551 baseEnd_4447551 := by
    simpa [prefixWord, tailWord_4447551, baseEnd_4447551] using wordTrace_append hprefix tailTrace_4447551
  have hstable : (prefixWord ++ tailWord_4447551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447551).length < 2 ^ (prefixWord ++ tailWord_4447551).sum := by decide
  have hdescent : baseEnd_4447551 < baseStart_4447551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447575 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_4447575 : Nat := 118140960795 + 4447575 * 2 ^ 59
def prefixEnd_4447575 : Nat := 4983230072969 + 3 ^ 40 * 4447575 * 2
def baseEnd_4447575 : Nat := 2283743721920541576058481

theorem tailTrace_4447575 : CollatzResearch.WordTrace tailWord_4447575 prefixEnd_4447575 2283743721920541576058481 := by
  unfold tailWord_4447575
  simp only [CollatzResearch.WordTrace]
  refine ⟨162216386862202835181432179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108144257908135223454288119 162216386862202835181432179)
  ·
    refine ⟨243324580293304252772148269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162216386862202835181432179 243324580293304252772148269)
    ·
      refine ⟨91246717609989094789555601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243324580293304252772148269 91246717609989094789555601)
      ·
        refine ⟨68435038207491821092166701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91246717609989094789555601 68435038207491821092166701)
        ·
          refine ⟨25663139327809432909562513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68435038207491821092166701 25663139327809432909562513)
          ·
            refine ⟨19247354495857074682171885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25663139327809432909562513 19247354495857074682171885)
            ·
              refine ⟨7217757935946403005814457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19247354495857074682171885 7217757935946403005814457)
              ·
                refine ⟨5413318451959802254360843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217757935946403005814457 5413318451959802254360843)
                ·
                  refine ⟨8119977677939703381541265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5413318451959802254360843 8119977677939703381541265)
                  ·
                    refine ⟨6089983258454777536155949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8119977677939703381541265 6089983258454777536155949)
                    ·
                      refine ⟨2283743721920541576058481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6089983258454777536155949 2283743721920541576058481)
                      ·
                        rfl

theorem cell23_4447575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_4447575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447575 prefixEnd_4447575 := by exact prefixLift 4447575
  have htrace : WordTrace (prefixWord ++ tailWord_4447575) baseStart_4447575 baseEnd_4447575 := by
    simpa [prefixWord, tailWord_4447575, baseEnd_4447575] using wordTrace_append hprefix tailTrace_4447575
  have hstable : (prefixWord ++ tailWord_4447575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447575).length < 2 ^ (prefixWord ++ tailWord_4447575).sum := by decide
  have hdescent : baseEnd_4447575 < baseStart_4447575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447588 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_4447588 : Nat := 118140960795 + 4447588 * 2 ^ 59
def prefixEnd_4447588 : Nat := 4983230072969 + 3 ^ 40 * 4447588 * 2
def baseEnd_4447588 : Nat := 2283750397169050025195921

theorem tailTrace_4447588 : CollatzResearch.WordTrace tailWord_4447588 prefixEnd_4447588 2283750397169050025195921 := by
  unfold tailWord_4447588
  simp only [CollatzResearch.WordTrace]
  refine ⟨81108430505577869200827709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108144574007437158934436945 81108430505577869200827709)
  ·
    refine ⟨30415661439591700950310391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81108430505577869200827709 30415661439591700950310391)
    ·
      refine ⟨45623492159387551425465587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30415661439591700950310391 45623492159387551425465587)
      ·
        refine ⟨68435238239081327138198381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45623492159387551425465587 68435238239081327138198381)
        ·
          refine ⟨25663214339655497676824393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68435238239081327138198381 25663214339655497676824393)
          ·
            refine ⟨19247410754741623257618295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25663214339655497676824393 19247410754741623257618295)
            ·
              refine ⟨28871116132112434886427443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19247410754741623257618295 28871116132112434886427443)
              ·
                refine ⟨43306674198168652329641165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28871116132112434886427443 43306674198168652329641165)
                ·
                  refine ⟨16240002824313244623615437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43306674198168652329641165 16240002824313244623615437)
                  ·
                    refine ⟨6090001059117466733855789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16240002824313244623615437 6090001059117466733855789)
                    ·
                      refine ⟨2283750397169050025195921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090001059117466733855789 2283750397169050025195921)
                      ·
                        rfl

theorem cell23_4447588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_4447588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447588 prefixEnd_4447588 := by exact prefixLift 4447588
  have htrace : WordTrace (prefixWord ++ tailWord_4447588) baseStart_4447588 baseEnd_4447588 := by
    simpa [prefixWord, tailWord_4447588, baseEnd_4447588] using wordTrace_append hprefix tailTrace_4447588
  have hstable : (prefixWord ++ tailWord_4447588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447588).length < 2 ^ (prefixWord ++ tailWord_4447588).sum := by decide
  have hdescent : baseEnd_4447588 < baseStart_4447588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447592 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4447592 : Nat := 118140960795 + 4447592 * 2 ^ 59
def prefixEnd_4447592 : Nat := 4983230072969 + 3 ^ 40 * 4447592 * 2
def baseEnd_4447592 : Nat := 2283752451091668009545903

theorem tailTrace_4447592 : CollatzResearch.WordTrace tailWord_4447592 prefixEnd_4447592 2283752451091668009545903 := by
  unfold tailWord_4447592
  simp only [CollatzResearch.WordTrace]
  refine ⟨81108503451570623542400515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108144671268760831389867353 81108503451570623542400515)
  ·
    refine ⟨121662755177355935313600773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81108503451570623542400515 121662755177355935313600773)
    ·
      refine ⟨22811766595754237871300145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121662755177355935313600773 22811766595754237871300145)
      ·
        refine ⟨17108824946815678403475109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22811766595754237871300145 17108824946815678403475109)
        ·
          refine ⟨3207904677527939700651583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17108824946815678403475109 3207904677527939700651583)
          ·
            refine ⟨4811857016291909550977375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207904677527939700651583 4811857016291909550977375)
            ·
              refine ⟨7217785524437864326466063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811857016291909550977375 7217785524437864326466063)
              ·
                refine ⟨10826678286656796489699095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217785524437864326466063 10826678286656796489699095)
                ·
                  refine ⟨16240017429985194734548643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10826678286656796489699095 16240017429985194734548643)
                  ·
                    refine ⟨24360026144977792101822965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16240017429985194734548643 24360026144977792101822965)
                    ·
                      refine ⟨2283752451091668009545903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24360026144977792101822965 2283752451091668009545903)
                      ·
                        rfl

theorem cell23_4447592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4447592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447592 prefixEnd_4447592 := by exact prefixLift 4447592
  have htrace : WordTrace (prefixWord ++ tailWord_4447592) baseStart_4447592 baseEnd_4447592 := by
    simpa [prefixWord, tailWord_4447592, baseEnd_4447592] using wordTrace_append hprefix tailTrace_4447592
  have hstable : (prefixWord ++ tailWord_4447592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447592).length < 2 ^ (prefixWord ++ tailWord_4447592).sum := by decide
  have hdescent : baseEnd_4447592 < baseStart_4447592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447601 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_4447601 : Nat := 118140960795 + 4447601 * 2 ^ 59
def prefixEnd_4447601 : Nat := 4983230072969 + 3 ^ 40 * 4447601 * 2
def baseEnd_4447601 : Nat := 2283757072417558474333361

theorem tailTrace_4447601 : CollatzResearch.WordTrace tailWord_4447601 prefixEnd_4447601 2283757072417558474333361 := by
  unfold tailWord_4447601
  simp only [CollatzResearch.WordTrace]
  refine ⟨162217335160108641621878657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108144890106739094414585771 162217335160108641621878657)
  ·
    refine ⟨121663001370081481216408993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162217335160108641621878657 121663001370081481216408993)
    ·
      refine ⟨91247251027561110912306745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121663001370081481216408993 91247251027561110912306745)
      ·
        refine ⟨68435438270670833184230059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91247251027561110912306745 68435438270670833184230059)
        ·
          refine ⟨102653157406006249776345089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68435438270670833184230059 102653157406006249776345089)
          ·
            refine ⟨76989868054504687332258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102653157406006249776345089 76989868054504687332258817)
            ·
              refine ⟨57742401040878515499194113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76989868054504687332258817 57742401040878515499194113)
              ·
                refine ⟨43306800780658886624395585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57742401040878515499194113 43306800780658886624395585)
                ·
                  refine ⟨32480100585494164968296689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43306800780658886624395585 32480100585494164968296689)
                  ·
                    refine ⟨24360075439120623726222517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32480100585494164968296689 24360075439120623726222517)
                    ·
                      refine ⟨2283757072417558474333361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24360075439120623726222517 2283757072417558474333361)
                      ·
                        rfl

theorem cell23_4447601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_4447601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447601 prefixEnd_4447601 := by exact prefixLift 4447601
  have htrace : WordTrace (prefixWord ++ tailWord_4447601) baseStart_4447601 baseEnd_4447601 := by
    simpa [prefixWord, tailWord_4447601, baseEnd_4447601] using wordTrace_append hprefix tailTrace_4447601
  have hstable : (prefixWord ++ tailWord_4447601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447601).length < 2 ^ (prefixWord ++ tailWord_4447601).sum := by decide
  have hdescent : baseEnd_4447601 < baseStart_4447601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447611 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_4447611 : Nat := 118140960795 + 4447611 * 2 ^ 59
def prefixEnd_4447611 : Nat := 4983230072969 + 3 ^ 40 * 4447611 * 2
def baseEnd_4447611 : Nat := 2283762207224103435208315

theorem tailTrace_4447611 : CollatzResearch.WordTrace tailWord_4447611 prefixEnd_4447611 2283762207224103435208315 := by
  unfold tailWord_4447611
  simp only [CollatzResearch.WordTrace]
  refine ⟨162217699890072413329742687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108145133260048275553161791 162217699890072413329742687)
  ·
    refine ⟨243326549835108619994614031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162217699890072413329742687 243326549835108619994614031)
    ·
      refine ⟨364989824752662929991921047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243326549835108619994614031 364989824752662929991921047)
      ·
        refine ⟨547484737128994394987881571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364989824752662929991921047 547484737128994394987881571)
        ·
          refine ⟨821227105693491592481822357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547484737128994394987881571 821227105693491592481822357)
          ·
            refine ⟨38495020579382418397585423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 821227105693491592481822357 38495020579382418397585423)
            ·
              refine ⟨57742530869073627596378135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38495020579382418397585423 57742530869073627596378135)
              ·
                refine ⟨86613796303610441394567203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57742530869073627596378135 86613796303610441394567203)
                ·
                  refine ⟨129920694455415662091850805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86613796303610441394567203 129920694455415662091850805)
                  ·
                    refine ⟨12180065105195218321111013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 129920694455415662091850805 12180065105195218321111013)
                    ·
                      refine ⟨2283762207224103435208315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12180065105195218321111013 2283762207224103435208315)
                      ·
                        rfl

theorem cell23_4447611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_4447611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447611 prefixEnd_4447611 := by exact prefixLift 4447611
  have htrace : WordTrace (prefixWord ++ tailWord_4447611) baseStart_4447611 baseEnd_4447611 := by
    simpa [prefixWord, tailWord_4447611, baseEnd_4447611] using wordTrace_append hprefix tailTrace_4447611
  have hstable : (prefixWord ++ tailWord_4447611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447611).length < 2 ^ (prefixWord ++ tailWord_4447611).sum := by decide
  have hdescent : baseEnd_4447611 < baseStart_4447611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447621 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_4447621 : Nat := 118140960795 + 4447621 * 2 ^ 59
def prefixEnd_4447621 : Nat := 4983230072969 + 3 ^ 40 * 4447621 * 2
def baseEnd_4447621 : Nat := 761255780676882798694423

theorem tailTrace_4447621 : CollatzResearch.WordTrace tailWord_4447621 prefixEnd_4447621 761255780676882798694423 := by
  unfold tailWord_4447621
  simp only [CollatzResearch.WordTrace]
  refine ⟨162218064620036185037606717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108145376413357456691737811 162218064620036185037606717)
  ·
    refine ⟨60831774232513569389102519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162218064620036185037606717 60831774232513569389102519)
    ·
      refine ⟨91247661348770354083653779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60831774232513569389102519 91247661348770354083653779)
      ·
        refine ⟨136871492023155531125480669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91247661348770354083653779 136871492023155531125480669)
        ·
          refine ⟨51326809508683324172055251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136871492023155531125480669 51326809508683324172055251)
          ·
            refine ⟨76990214263024986258082877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51326809508683324172055251 76990214263024986258082877)
            ·
              refine ⟨28871330348634369846781079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76990214263024986258082877 28871330348634369846781079)
              ·
                refine ⟨43306995522951554770171619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28871330348634369846781079 43306995522951554770171619)
                ·
                  refine ⟨64960493284427332155257429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43306995522951554770171619 64960493284427332155257429)
                  ·
                    refine ⟨761255780676882798694423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64960493284427332155257429 761255780676882798694423)
                    ·
                      rfl

theorem cell23_4447621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_4447621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447621 prefixEnd_4447621 := by exact prefixLift 4447621
  have htrace : WordTrace (prefixWord ++ tailWord_4447621) baseStart_4447621 baseEnd_4447621 := by
    simpa [prefixWord, tailWord_4447621, baseEnd_4447621] using wordTrace_append hprefix tailTrace_4447621
  have hstable : (prefixWord ++ tailWord_4447621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447621).length < 2 ^ (prefixWord ++ tailWord_4447621).sum := by decide
  have hdescent : baseEnd_4447621 < baseStart_4447621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447651 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 9]
def baseStart_4447651 : Nat := 118140960795 + 4447651 * 2 ^ 59
def prefixEnd_4447651 : Nat := 4983230072969 + 3 ^ 40 * 4447651 * 2
def baseEnd_4447651 : Nat := 253753638494475919856459

theorem tailTrace_4447651 : CollatzResearch.WordTrace tailWord_4447651 prefixEnd_4447651 253753638494475919856459 := by
  unfold tailWord_4447651
  simp only [CollatzResearch.WordTrace]
  refine ⟨162219158809927500161198807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108146105873285000107465871 162219158809927500161198807)
  ·
    refine ⟨243328738214891250241798211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162219158809927500161198807 243328738214891250241798211)
    ·
      refine ⟨364993107322336875362697317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243328738214891250241798211 364993107322336875362697317)
      ·
        refine ⟨68436207622938164130505747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364993107322336875362697317 68436207622938164130505747)
        ·
          refine ⟨102654311434407246195758621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68436207622938164130505747 102654311434407246195758621)
          ·
            refine ⟨38495366787902717323409483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102654311434407246195758621 38495366787902717323409483)
            ·
              refine ⟨57743050181854075985114225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38495366787902717323409483 57743050181854075985114225)
              ·
                refine ⟨43307287636390556988835669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57743050181854075985114225 43307287636390556988835669)
                ·
                  refine ⟨253753638494475919856459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43307287636390556988835669 253753638494475919856459)
                  ·
                    rfl

theorem cell23_4447651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 9].length) (baseStart_4447651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447651 prefixEnd_4447651 := by exact prefixLift 4447651
  have htrace : WordTrace (prefixWord ++ tailWord_4447651) baseStart_4447651 baseEnd_4447651 := by
    simpa [prefixWord, tailWord_4447651, baseEnd_4447651] using wordTrace_append hprefix tailTrace_4447651
  have hstable : (prefixWord ++ tailWord_4447651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447651).length < 2 ^ (prefixWord ++ tailWord_4447651).sum := by decide
  have hdescent : baseEnd_4447651 < baseStart_4447651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447656 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4447656 : Nat := 118140960795 + 4447656 * 2 ^ 59
def prefixEnd_4447656 : Nat := 4983230072969 + 3 ^ 40 * 4447656 * 2
def baseEnd_4447656 : Nat := 2283785313853555759145609

theorem tailTrace_4447656 : CollatzResearch.WordTrace tailWord_4447656 prefixEnd_4447656 2283785313853555759145609 := by
  unfold tailWord_4447656
  simp only [CollatzResearch.WordTrace]
  refine ⟨81109670587454693007565411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108146227449939590676753881 81109670587454693007565411)
  ·
    refine ⟨121664505881182039511348117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81109670587454693007565411 121664505881182039511348117)
    ·
      refine ⟨5703023713180408102094443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121664505881182039511348117 5703023713180408102094443)
      ·
        refine ⟨8554535569770612153141665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703023713180408102094443 8554535569770612153141665)
        ·
          refine ⟨6415901677327959114856249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8554535569770612153141665 6415901677327959114856249)
          ·
            refine ⟨4811926257995969336142187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6415901677327959114856249 4811926257995969336142187)
            ·
              refine ⟨7217889386993954004213281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811926257995969336142187 7217889386993954004213281)
              ·
                refine ⟨5413417040245465503159961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217889386993954004213281 5413417040245465503159961)
                ·
                  refine ⟨4060062780184099127369971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413417040245465503159961 4060062780184099127369971)
                  ·
                    refine ⟨6090094170276148691054957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060062780184099127369971 6090094170276148691054957)
                    ·
                      refine ⟨2283785313853555759145609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090094170276148691054957 2283785313853555759145609)
                      ·
                        rfl

theorem cell23_4447656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4447656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447656 prefixEnd_4447656 := by exact prefixLift 4447656
  have htrace : WordTrace (prefixWord ++ tailWord_4447656) baseStart_4447656 baseEnd_4447656 := by
    simpa [prefixWord, tailWord_4447656, baseEnd_4447656] using wordTrace_append hprefix tailTrace_4447656
  have hstable : (prefixWord ++ tailWord_4447656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447656).length < 2 ^ (prefixWord ++ tailWord_4447656).sum := by decide
  have hdescent : baseEnd_4447656 < baseStart_4447656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447715 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 2, 5]
def baseStart_4447715 : Nat := 118140960795 + 4447715 * 2 ^ 59
def prefixEnd_4447715 : Nat := 4983230072969 + 3 ^ 40 * 4447715 * 2
def baseEnd_4447715 : Nat := 761271869737390342769279

theorem tailTrace_4447715 : CollatzResearch.WordTrace tailWord_4447715 prefixEnd_4447715 761271869737390342769279 := by
  unfold tailWord_4447715
  simp only [CollatzResearch.WordTrace]
  refine ⟨162221493081695639091528599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108147662054463759394352399 162221493081695639091528599)
  ·
    refine ⟨243332239622543458637292899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162221493081695639091528599 243332239622543458637292899)
    ·
      refine ⟨364998359433815187955939349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243332239622543458637292899 364998359433815187955939349)
      ·
        refine ⟨17109298098460086935434657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 364998359433815187955939349 17109298098460086935434657)
        ·
          refine ⟨12831973573845065201575993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17109298098460086935434657 12831973573845065201575993)
          ·
            refine ⟨9623980180383798901181995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12831973573845065201575993 9623980180383798901181995)
            ·
              refine ⟨14435970270575698351772993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623980180383798901181995 14435970270575698351772993)
              ·
                refine ⟨10826977702931773763829745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14435970270575698351772993 10826977702931773763829745)
                ·
                  refine ⟨8120233277198830322872309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10826977702931773763829745 8120233277198830322872309)
                  ·
                    refine ⟨761271869737390342769279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8120233277198830322872309 761271869737390342769279)
                    ·
                      rfl

theorem cell23_4447715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].length) (baseStart_4447715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447715 prefixEnd_4447715 := by exact prefixLift 4447715
  have htrace : WordTrace (prefixWord ++ tailWord_4447715) baseStart_4447715 baseEnd_4447715 := by
    simpa [prefixWord, tailWord_4447715, baseEnd_4447715] using wordTrace_append hprefix tailTrace_4447715
  have hstable : (prefixWord ++ tailWord_4447715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447715).length < 2 ^ (prefixWord ++ tailWord_4447715).sum := by decide
  have hdescent : baseEnd_4447715 < baseStart_4447715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447779 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 1, 4]
def baseStart_4447779 : Nat := 118140960795 + 4447779 * 2 ^ 59
def prefixEnd_4447779 : Nat := 4983230072969 + 3 ^ 40 * 4447779 * 2
def baseEnd_4447779 : Nat := 761282823991352925969181

theorem tailTrace_4447779 : CollatzResearch.WordTrace tailWord_4447779 prefixEnd_4447779 761282823991352925969181 := by
  unfold tailWord_4447779
  simp only [CollatzResearch.WordTrace]
  refine ⟨162223827353463778021858391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108149218235642518681238927 162223827353463778021858391)
  ·
    refine ⟨243335741030195667032787587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162223827353463778021858391 243335741030195667032787587)
    ·
      refine ⟨365003611545293500549181381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243335741030195667032787587 365003611545293500549181381)
      ·
        refine ⟨68438177164742531352971509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 365003611545293500549181381 68438177164742531352971509)
        ·
          refine ⟨6416079109194612314341079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68438177164742531352971509 6416079109194612314341079)
          ·
            refine ⟨9624118663791918471511619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416079109194612314341079 9624118663791918471511619)
            ·
              refine ⟨14436177995687877707267429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624118663791918471511619 14436177995687877707267429)
              ·
                refine ⟨2706783374191477070112643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14436177995687877707267429 2706783374191477070112643)
                ·
                  refine ⟨4060175061287215605168965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706783374191477070112643 4060175061287215605168965)
                  ·
                    refine ⟨761282823991352925969181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060175061287215605168965 761282823991352925969181)
                    ·
                      rfl

theorem cell23_4447779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 4].length) (baseStart_4447779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447779 prefixEnd_4447779 := by exact prefixLift 4447779
  have htrace : WordTrace (prefixWord ++ tailWord_4447779) baseStart_4447779 baseEnd_4447779 := by
    simpa [prefixWord, tailWord_4447779, baseEnd_4447779] using wordTrace_append hprefix tailTrace_4447779
  have hstable : (prefixWord ++ tailWord_4447779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447779).length < 2 ^ (prefixWord ++ tailWord_4447779).sum := by decide
  have hdescent : baseEnd_4447779 < baseStart_4447779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447802 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_4447802 : Nat := 118140960795 + 4447802 * 2 ^ 59
def prefixEnd_4447802 : Nat := 4983230072969 + 3 ^ 40 * 4447802 * 2
def baseEnd_4447802 : Nat := 2283860282029112187919937

theorem tailTrace_4447802 : CollatzResearch.WordTrace tailWord_4447802 prefixEnd_4447802 2283860282029112187919937 := by
  unfold tailWord_4447802
  simp only [CollatzResearch.WordTrace]
  refine ⟨40556166558095113237486415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108149777488253635299963773 40556166558095113237486415)
  ·
    refine ⟨60834249837142669856229623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40556166558095113237486415 60834249837142669856229623)
    ·
      refine ⟨91251374755714004784344435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60834249837142669856229623 91251374755714004784344435)
      ·
        refine ⟨136877062133571007176516653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91251374755714004784344435 136877062133571007176516653)
        ·
          refine ⟨51328898300089127691193745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136877062133571007176516653 51328898300089127691193745)
          ·
            refine ⟨38496673725066845768395309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51328898300089127691193745 38496673725066845768395309)
            ·
              refine ⟨14436252646900067163148241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38496673725066845768395309 14436252646900067163148241)
              ·
                refine ⟨10827189485175050372361181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14436252646900067163148241 10827189485175050372361181)
                ·
                  refine ⟨4060196056940643889635443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10827189485175050372361181 4060196056940643889635443)
                  ·
                    refine ⟨6090294085410965834453165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060196056940643889635443 6090294085410965834453165)
                    ·
                      refine ⟨2283860282029112187919937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090294085410965834453165 2283860282029112187919937)
                      ·
                        rfl

theorem cell23_4447802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_4447802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447802 prefixEnd_4447802 := by exact prefixLift 4447802
  have htrace : WordTrace (prefixWord ++ tailWord_4447802) baseStart_4447802 baseEnd_4447802 := by
    simpa [prefixWord, tailWord_4447802, baseEnd_4447802] using wordTrace_append hprefix tailTrace_4447802
  have hstable : (prefixWord ++ tailWord_4447802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447802).length < 2 ^ (prefixWord ++ tailWord_4447802).sum := by decide
  have hdescent : baseEnd_4447802 < baseStart_4447802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447836 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4447836 : Nat := 118140960795 + 4447836 * 2 ^ 59
def prefixEnd_4447836 : Nat := 4983230072969 + 3 ^ 40 * 4447836 * 2
def baseEnd_4447836 : Nat := 2283877740371365054894781

theorem tailTrace_4447836 : CollatzResearch.WordTrace tailWord_4447836 prefixEnd_4447836 2283877740371365054894781 := by
  unfold tailWord_4447836
  simp only [CollatzResearch.WordTrace]
  refine ⟨81112953157128638378341681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108150604209504851171122241 81112953157128638378341681)
  ·
    refine ⟨60834714867846478783756261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81112953157128638378341681 60834714867846478783756261)
    ·
      refine ⟨11406509037721214771954299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60834714867846478783756261 11406509037721214771954299)
      ·
        refine ⟨17109763556581822157931449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11406509037721214771954299 17109763556581822157931449)
        ·
          refine ⟨12832322667436366618448587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17109763556581822157931449 12832322667436366618448587)
          ·
            refine ⟨19248484001154549927672881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12832322667436366618448587 19248484001154549927672881)
            ·
              refine ⟨14436363000865912445754661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19248484001154549927672881 14436363000865912445754661)
              ·
                refine ⟨2706818062662358583578999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14436363000865912445754661 2706818062662358583578999)
                ·
                  refine ⟨4060227093993537875368499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706818062662358583578999 4060227093993537875368499)
                  ·
                    refine ⟨6090340640990306813052749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060227093993537875368499 6090340640990306813052749)
                    ·
                      refine ⟨2283877740371365054894781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090340640990306813052749 2283877740371365054894781)
                      ·
                        rfl

theorem cell23_4447836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4447836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447836 prefixEnd_4447836 := by exact prefixLift 4447836
  have htrace : WordTrace (prefixWord ++ tailWord_4447836) baseStart_4447836 baseEnd_4447836 := by
    simpa [prefixWord, tailWord_4447836, baseEnd_4447836] using wordTrace_append hprefix tailTrace_4447836
  have hstable : (prefixWord ++ tailWord_4447836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447836).length < 2 ^ (prefixWord ++ tailWord_4447836).sum := by decide
  have hdescent : baseEnd_4447836 < baseStart_4447836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447845 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4447845 : Nat := 118140960795 + 4447845 * 2 ^ 59
def prefixEnd_4447845 : Nat := 4983230072969 + 3 ^ 40 * 4447845 * 2
def baseEnd_4447845 : Nat := 2283882361697255519682239

theorem tailTrace_4447845 : CollatzResearch.WordTrace tailWord_4447845 prefixEnd_4447845 2283882361697255519682239 := by
  unfold tailWord_4447845
  simp only [CollatzResearch.WordTrace]
  refine ⟨162226234571224671293760989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108150823047483114195840659 162226234571224671293760989)
  ·
    refine ⟨60834837964209251735160371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162226234571224671293760989 60834837964209251735160371)
    ·
      refine ⟨91252256946313877602740557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60834837964209251735160371 91252256946313877602740557)
      ·
        refine ⟨34219596354867704101027709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91252256946313877602740557 34219596354867704101027709)
        ·
          refine ⟨12832348633075389037885391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34219596354867704101027709 12832348633075389037885391)
          ·
            refine ⟨19248522949613083556828087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12832348633075389037885391 19248522949613083556828087)
            ·
              refine ⟨28872784424419625335242131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19248522949613083556828087 28872784424419625335242131)
              ·
                refine ⟨43309176636629438002863197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28872784424419625335242131 43309176636629438002863197)
                ·
                  refine ⟨16240941238736039251073699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43309176636629438002863197 16240941238736039251073699)
                  ·
                    refine ⟨24361411858104058876610549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16240941238736039251073699 24361411858104058876610549)
                    ·
                      refine ⟨2283882361697255519682239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24361411858104058876610549 2283882361697255519682239)
                      ·
                        rfl

theorem cell23_4447845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4447845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447845 prefixEnd_4447845 := by exact prefixLift 4447845
  have htrace : WordTrace (prefixWord ++ tailWord_4447845) baseStart_4447845 baseEnd_4447845 := by
    simpa [prefixWord, tailWord_4447845, baseEnd_4447845] using wordTrace_append hprefix tailTrace_4447845
  have hstable : (prefixWord ++ tailWord_4447845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447845).length < 2 ^ (prefixWord ++ tailWord_4447845).sum := by decide
  have hdescent : baseEnd_4447845 < baseStart_4447845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447875 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3]
def baseStart_4447875 : Nat := 118140960795 + 4447875 * 2 ^ 59
def prefixEnd_4447875 : Nat := 4983230072969 + 3 ^ 40 * 4447875 * 2
def baseEnd_4447875 : Nat := 2283897766116890402307101

theorem tailTrace_4447875 : CollatzResearch.WordTrace tailWord_4447875 prefixEnd_4447875 2283897766116890402307101 := by
  unfold tailWord_4447875
  simp only [CollatzResearch.WordTrace]
  refine ⟨162227328761115986417353079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108151552507410657611568719 162227328761115986417353079)
  ·
    refine ⟨243340993141673979626029619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162227328761115986417353079 243340993141673979626029619)
    ·
      refine ⟨365011489712510969439044429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243340993141673979626029619 365011489712510969439044429)
      ·
        refine ⟨136879308642191613539641661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365011489712510969439044429 136879308642191613539641661)
        ·
          refine ⟨51329740740821855077365623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136879308642191613539641661 51329740740821855077365623)
          ·
            refine ⟨76994611111232782616048435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51329740740821855077365623 76994611111232782616048435)
            ·
              refine ⟨115491916666849173924072653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76994611111232782616048435 115491916666849173924072653)
              ·
                refine ⟨43309468750068440221527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115491916666849173924072653 43309468750068440221527245)
                ·
                  refine ⟨16241050781275665083072717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43309468750068440221527245 16241050781275665083072717)
                  ·
                    refine ⟨6090394042978374406152269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16241050781275665083072717 6090394042978374406152269)
                    ·
                      refine ⟨2283897766116890402307101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090394042978374406152269 2283897766116890402307101)
                      ·
                        rfl

theorem cell23_4447875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_4447875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447875 prefixEnd_4447875 := by exact prefixLift 4447875
  have htrace : WordTrace (prefixWord ++ tailWord_4447875) baseStart_4447875 baseEnd_4447875 := by
    simpa [prefixWord, tailWord_4447875, baseEnd_4447875] using wordTrace_append hprefix tailTrace_4447875
  have hstable : (prefixWord ++ tailWord_4447875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447875).length < 2 ^ (prefixWord ++ tailWord_4447875).sum := by decide
  have hdescent : baseEnd_4447875 < baseStart_4447875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447903 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 2, 4]
def baseStart_4447903 : Nat := 118140960795 + 4447903 * 2 ^ 59
def prefixEnd_4447903 : Nat := 4983230072969 + 3 ^ 40 * 4447903 * 2
def baseEnd_4447903 : Nat := 761304047858405430918991

theorem tailTrace_4447903 : CollatzResearch.WordTrace tailWord_4447903 prefixEnd_4447903 761304047858405430918991 := by
  unfold tailWord_4447903
  simp only [CollatzResearch.WordTrace]
  refine ⟨162228350005014547199372363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108152233336676364799581575 162228350005014547199372363)
  ·
    refine ⟨243342525007521820799058545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162228350005014547199372363 243342525007521820799058545)
    ·
      refine ⟨182506893755641365599293909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243342525007521820799058545 182506893755641365599293909)
      ·
        refine ⟨4277505322397844506233451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 182506893755641365599293909 4277505322397844506233451)
        ·
          refine ⟨6416257983596766759350177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277505322397844506233451 6416257983596766759350177)
          ·
            refine ⟨4812193487697575069512633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6416257983596766759350177 4812193487697575069512633)
            ·
              refine ⟨3609145115773181302134475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4812193487697575069512633 3609145115773181302134475)
              ·
                refine ⟨5413717673659771953201713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609145115773181302134475 5413717673659771953201713)
                ·
                  refine ⟨4060288255244828964901285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413717673659771953201713 4060288255244828964901285)
                  ·
                    refine ⟨761304047858405430918991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060288255244828964901285 761304047858405430918991)
                    ·
                      rfl

theorem cell23_4447903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_4447903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447903 prefixEnd_4447903 := by exact prefixLift 4447903
  have htrace : WordTrace (prefixWord ++ tailWord_4447903) baseStart_4447903 baseEnd_4447903 := by
    simpa [prefixWord, tailWord_4447903, baseEnd_4447903] using wordTrace_append hprefix tailTrace_4447903
  have hstable : (prefixWord ++ tailWord_4447903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447903).length < 2 ^ (prefixWord ++ tailWord_4447903).sum := by decide
  have hdescent : baseEnd_4447903 < baseStart_4447903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447926 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4447926 : Nat := 118140960795 + 4447926 * 2 ^ 59
def prefixEnd_4447926 : Nat := 4983230072969 + 3 ^ 40 * 4447926 * 2
def baseEnd_4447926 : Nat := 2283923953630269702769367

theorem tailTrace_4447926 : CollatzResearch.WordTrace tailWord_4447926 prefixEnd_4447926 2283923953630269702769367 := by
  unfold tailWord_4447926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139324305245701382966227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108152792589287481418306421 10139324305245701382966227)
  ·
    refine ⟨15208986457868552074449341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10139324305245701382966227 15208986457868552074449341)
    ·
      refine ⟨5703369921700707027918503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15208986457868552074449341 5703369921700707027918503)
      ·
        refine ⟨8555054882551060541877755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703369921700707027918503 8555054882551060541877755)
        ·
          refine ⟨12832582323826590812816633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555054882551060541877755 12832582323826590812816633)
          ·
            refine ⟨9624436742869943109612475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12832582323826590812816633 9624436742869943109612475)
            ·
              refine ⟨14436655114304914664418713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624436742869943109612475 14436655114304914664418713)
              ·
                refine ⟨10827491335728685998314035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14436655114304914664418713 10827491335728685998314035)
                ·
                  refine ⟨16241237003593028997471053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10827491335728685998314035 16241237003593028997471053)
                  ·
                    refine ⟨6090463876347385874051645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16241237003593028997471053 6090463876347385874051645)
                    ·
                      refine ⟨2283923953630269702769367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090463876347385874051645 2283923953630269702769367)
                      ·
                        rfl

theorem cell23_4447926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4447926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447926 prefixEnd_4447926 := by exact prefixLift 4447926
  have htrace : WordTrace (prefixWord ++ tailWord_4447926) baseStart_4447926 baseEnd_4447926 := by
    simpa [prefixWord, tailWord_4447926, baseEnd_4447926] using wordTrace_append hprefix tailTrace_4447926
  have hstable : (prefixWord ++ tailWord_4447926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447926).length < 2 ^ (prefixWord ++ tailWord_4447926).sum := by decide
  have hdescent : baseEnd_4447926 < baseStart_4447926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447935 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_4447935 : Nat := 118140960795 + 4447935 * 2 ^ 59
def prefixEnd_4447935 : Nat := 4983230072969 + 3 ^ 40 * 4447935 * 2
def baseEnd_4447935 : Nat := 2283928574956160167556825

theorem tailTrace_4447935 : CollatzResearch.WordTrace tailWord_4447935 prefixEnd_4447935 2283928574956160167556825 := by
  unfold tailWord_4447935
  simp only [CollatzResearch.WordTrace]
  refine ⟨162229517140898616664537259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108153011427265744443024839 162229517140898616664537259)
  ·
    refine ⟨243344275711347924996805889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162229517140898616664537259 243344275711347924996805889)
    ·
      refine ⟨182508206783510943747604417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243344275711347924996805889 182508206783510943747604417)
      ·
        refine ⟨136881155087633207810703313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182508206783510943747604417 136881155087633207810703313)
        ·
          refine ⟨102660866315724905858027485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136881155087633207810703313 102660866315724905858027485)
          ·
            refine ⟨38497824868396839696760307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102660866315724905858027485 38497824868396839696760307)
            ·
              refine ⟨57746737302595259545140461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38497824868396839696760307 57746737302595259545140461)
              ·
                refine ⟨21655026488473222329427673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57746737302595259545140461 21655026488473222329427673)
                ·
                  refine ⟨16241269866354916747070755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21655026488473222329427673 16241269866354916747070755)
                  ·
                    refine ⟨24361904799532375120606133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16241269866354916747070755 24361904799532375120606133)
                    ·
                      refine ⟨2283928574956160167556825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24361904799532375120606133 2283928574956160167556825)
                      ·
                        rfl

theorem cell23_4447935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_4447935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447935 prefixEnd_4447935 := by exact prefixLift 4447935
  have htrace : WordTrace (prefixWord ++ tailWord_4447935) baseStart_4447935 baseEnd_4447935 := by
    simpa [prefixWord, tailWord_4447935, baseEnd_4447935] using wordTrace_append hprefix tailTrace_4447935
  have hstable : (prefixWord ++ tailWord_4447935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447935).length < 2 ^ (prefixWord ++ tailWord_4447935).sum := by decide
  have hdescent : baseEnd_4447935 < baseStart_4447935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447936 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2]
def baseStart_4447936 : Nat := 118140960795 + 4447936 * 2 ^ 59
def prefixEnd_4447936 : Nat := 4983230072969 + 3 ^ 40 * 4447936 * 2
def baseEnd_4447936 : Nat := 2283929088436814663644321

theorem tailTrace_4447936 : CollatzResearch.WordTrace tailWord_4447936 prefixEnd_4447936 2283929088436814663644321 := by
  unfold tailWord_4447936
  simp only [CollatzResearch.WordTrace]
  refine ⟨81114776806947496917661831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108153035742596662556882441 81114776806947496917661831)
  ·
    refine ⟨121672165210421245376492747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81114776806947496917661831 121672165210421245376492747)
    ·
      refine ⟨182508247815631868064739121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121672165210421245376492747 182508247815631868064739121)
      ·
        refine ⟨136881185861723901048554341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182508247815631868064739121 136881185861723901048554341)
        ·
          refine ⟨25665222349073231446603939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136881185861723901048554341 25665222349073231446603939)
          ·
            refine ⟨38497833523609847169905909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25665222349073231446603939 38497833523609847169905909)
            ·
              refine ⟨3609171892838423172178679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38497833523609847169905909 3609171892838423172178679)
              ·
                refine ⟨5413757839257634758268019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609171892838423172178679 5413757839257634758268019)
                ·
                  refine ⟨8120636758886452137402029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5413757839257634758268019 8120636758886452137402029)
                  ·
                    refine ⟨3045238784582419551525761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8120636758886452137402029 3045238784582419551525761)
                    ·
                      refine ⟨2283929088436814663644321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045238784582419551525761 2283929088436814663644321)
                      ·
                        rfl

theorem cell23_4447936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_4447936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447936 prefixEnd_4447936 := by exact prefixLift 4447936
  have htrace : WordTrace (prefixWord ++ tailWord_4447936) baseStart_4447936 baseEnd_4447936 := by
    simpa [prefixWord, tailWord_4447936, baseEnd_4447936] using wordTrace_append hprefix tailTrace_4447936
  have hstable : (prefixWord ++ tailWord_4447936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447936).length < 2 ^ (prefixWord ++ tailWord_4447936).sum := by decide
  have hdescent : baseEnd_4447936 < baseStart_4447936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447949 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4447949 : Nat := 118140960795 + 4447949 * 2 ^ 59
def prefixEnd_4447949 : Nat := 4983230072969 + 3 ^ 40 * 4447949 * 2
def baseEnd_4447949 : Nat := 2283935763685323112781761

theorem tailTrace_4447949 : CollatzResearch.WordTrace tailWord_4447949 prefixEnd_4447949 2283935763685323112781761 := by
  unfold tailWord_4447949
  simp only [CollatzResearch.WordTrace]
  refine ⟨162230027762847897055546901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108153351841898598037031267 162230027762847897055546901)
  ·
    refine ⟨7604532551383495174478761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162230027762847897055546901 7604532551383495174478761)
    ·
      refine ⟨5703399413537621380859071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604532551383495174478761 5703399413537621380859071)
      ·
        refine ⟨8555099120306432071288607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703399413537621380859071 8555099120306432071288607)
        ·
          refine ⟨12832648680459648106932911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555099120306432071288607 12832648680459648106932911)
          ·
            refine ⟨19248973020689472160399367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12832648680459648106932911 19248973020689472160399367)
            ·
              refine ⟨28873459531034208240599051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19248973020689472160399367 28873459531034208240599051)
              ·
                refine ⟨43310189296551312360898577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28873459531034208240599051 43310189296551312360898577)
                ·
                  refine ⟨32482641972413484270673933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43310189296551312360898577 32482641972413484270673933)
                  ·
                    refine ⟨12180990739655056601502725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32482641972413484270673933 12180990739655056601502725)
                    ·
                      refine ⟨2283935763685323112781761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12180990739655056601502725 2283935763685323112781761)
                      ·
                        rfl

theorem cell23_4447949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4447949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447949 prefixEnd_4447949 := by exact prefixLift 4447949
  have htrace : WordTrace (prefixWord ++ tailWord_4447949) baseStart_4447949 baseEnd_4447949 := by
    simpa [prefixWord, tailWord_4447949, baseEnd_4447949] using wordTrace_append hprefix tailTrace_4447949
  have hstable : (prefixWord ++ tailWord_4447949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447949).length < 2 ^ (prefixWord ++ tailWord_4447949).sum := by decide
  have hdescent : baseEnd_4447949 < baseStart_4447949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447962 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4447962 : Nat := 118140960795 + 4447962 * 2 ^ 59
def prefixEnd_4447962 : Nat := 4983230072969 + 3 ^ 40 * 4447962 * 2
def baseEnd_4447962 : Nat := 2283942438933831561919201

theorem tailTrace_4447962 : CollatzResearch.WordTrace tailWord_4447962 prefixEnd_4447962 2283942438933831561919201 := by
  unfold tailWord_4447962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40557625477950200068942535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108153667941200533517180093 40557625477950200068942535)
  ·
    refine ⟨60836438216925300103413803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40557625477950200068942535 60836438216925300103413803)
    ·
      refine ⟨91254657325387950155120705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60836438216925300103413803 91254657325387950155120705)
      ·
        refine ⟨68440992994040962616340529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91254657325387950155120705 68440992994040962616340529)
        ·
          refine ⟨51330744745530721962255397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68440992994040962616340529 51330744745530721962255397)
          ·
            refine ⟨9624514639787010367922887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51330744745530721962255397 9624514639787010367922887)
            ·
              refine ⟨14436771959680515551884331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624514639787010367922887 14436771959680515551884331)
              ·
                refine ⟨21655157939520773327826497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14436771959680515551884331 21655157939520773327826497)
                ·
                  refine ⟨16241368454640579995869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21655157939520773327826497 16241368454640579995869873)
                  ·
                    refine ⟨12181026340980434996902405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16241368454640579995869873 12181026340980434996902405)
                    ·
                      refine ⟨2283942438933831561919201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12181026340980434996902405 2283942438933831561919201)
                      ·
                        rfl

theorem cell23_4447962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4447962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447962 prefixEnd_4447962 := by exact prefixLift 4447962
  have htrace : WordTrace (prefixWord ++ tailWord_4447962) baseStart_4447962 baseEnd_4447962 := by
    simpa [prefixWord, tailWord_4447962, baseEnd_4447962] using wordTrace_append hprefix tailTrace_4447962
  have hstable : (prefixWord ++ tailWord_4447962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447962).length < 2 ^ (prefixWord ++ tailWord_4447962).sum := by decide
  have hdescent : baseEnd_4447962 < baseStart_4447962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447982 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4447982 : Nat := 118140960795 + 4447982 * 2 ^ 59
def prefixEnd_4447982 : Nat := 4983230072969 + 3 ^ 40 * 4447982 * 2
def baseEnd_4447982 : Nat := 2283952708546921483669109

theorem tailTrace_4447982 : CollatzResearch.WordTrace tailWord_4447982 prefixEnd_4447982 2283952708546921483669109 := by
  unfold tailWord_4447982
  simp only [CollatzResearch.WordTrace]
  refine ⟨20278903921466042961437275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108154154247818895794332133 20278903921466042961437275)
  ·
    refine ⟨30418355882199064442155913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20278903921466042961437275 30418355882199064442155913)
    ·
      refine ⟨22813766911649298331616935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30418355882199064442155913 22813766911649298331616935)
      ·
        refine ⟨34220650367473947497425403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22813766911649298331616935 34220650367473947497425403)
        ·
          refine ⟨51330975551210921246138105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34220650367473947497425403 51330975551210921246138105)
          ·
            refine ⟨38498231663408190934603579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51330975551210921246138105 38498231663408190934603579)
            ·
              refine ⟨57747347495112286401905369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38498231663408190934603579 57747347495112286401905369)
              ·
                refine ⟨43310510621334214801429027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57747347495112286401905369 43310510621334214801429027)
                ·
                  refine ⟨64965765932001322202143541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43310510621334214801429027 64965765932001322202143541)
                  ·
                    refine ⟨6090540556125123956450957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64965765932001322202143541 6090540556125123956450957)
                    ·
                      refine ⟨2283952708546921483669109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090540556125123956450957 2283952708546921483669109)
                      ·
                        rfl

theorem cell23_4447982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4447982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447982 prefixEnd_4447982 := by exact prefixLift 4447982
  have htrace : WordTrace (prefixWord ++ tailWord_4447982) baseStart_4447982 baseEnd_4447982 := by
    simpa [prefixWord, tailWord_4447982, baseEnd_4447982] using wordTrace_append hprefix tailTrace_4447982
  have hstable : (prefixWord ++ tailWord_4447982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447982).length < 2 ^ (prefixWord ++ tailWord_4447982).sum := by decide
  have hdescent : baseEnd_4447982 < baseStart_4447982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447992 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_4447992 : Nat := 118140960795 + 4447992 * 2 ^ 59
def prefixEnd_4447992 : Nat := 4983230072969 + 3 ^ 40 * 4447992 * 2
def baseEnd_4447992 : Nat := 2283957843353466444544063

theorem tailTrace_4447992 : CollatzResearch.WordTrace tailWord_4447992 prefixEnd_4447992 2283957843353466444544063 := by
  unfold tailWord_4447992
  simp only [CollatzResearch.WordTrace]
  refine ⟨81115798050846057699681115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108154397401128076932908153 81115798050846057699681115)
  ·
    refine ⟨121673697076269086549521673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81115798050846057699681115 121673697076269086549521673)
    ·
      refine ⟨91255272807201814912141255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121673697076269086549521673 91255272807201814912141255)
      ·
        refine ⟨136882909210802722368211883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91255272807201814912141255 136882909210802722368211883)
        ·
          refine ⟨205324363816204083552317825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136882909210802722368211883 205324363816204083552317825)
          ·
            refine ⟨153993272862153062664238369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205324363816204083552317825 153993272862153062664238369)
            ·
              refine ⟨115494954646614796998178777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153993272862153062664238369 115494954646614796998178777)
              ·
                refine ⟨86621215984961097748634083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115494954646614796998178777 86621215984961097748634083)
                ·
                  refine ⟨129931823977441646622951125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86621215984961097748634083 129931823977441646622951125)
                  ·
                    refine ⟨3045277124471288592725417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129931823977441646622951125 3045277124471288592725417)
                    ·
                      refine ⟨2283957843353466444544063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045277124471288592725417 2283957843353466444544063)
                      ·
                        rfl

theorem cell23_4447992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_4447992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447992 prefixEnd_4447992 := by exact prefixLift 4447992
  have htrace : WordTrace (prefixWord ++ tailWord_4447992) baseStart_4447992 baseEnd_4447992 := by
    simpa [prefixWord, tailWord_4447992, baseEnd_4447992] using wordTrace_append hprefix tailTrace_4447992
  have hstable : (prefixWord ++ tailWord_4447992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447992).length < 2 ^ (prefixWord ++ tailWord_4447992).sum := by decide
  have hdescent : baseEnd_4447992 < baseStart_4447992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447995 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_4447995 : Nat := 118140960795 + 4447995 * 2 ^ 59
def prefixEnd_4447995 : Nat := 4983230072969 + 3 ^ 40 * 4447995 * 2
def baseEnd_4447995 : Nat := 2283959383795429932806549

theorem tailTrace_4447995 : CollatzResearch.WordTrace tailWord_4447995 prefixEnd_4447995 2283959383795429932806549 := by
  unfold tailWord_4447995
  simp only [CollatzResearch.WordTrace]
  refine ⟨162231705520681246911721439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108154470347120831274480959 162231705520681246911721439)
  ·
    refine ⟨243347558281021870367582159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162231705520681246911721439 243347558281021870367582159)
    ·
      refine ⟨365021337421532805551373239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243347558281021870367582159 365021337421532805551373239)
      ·
        refine ⟨547532006132299208327059859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365021337421532805551373239 547532006132299208327059859)
        ·
          refine ⟨821298009198448812490589789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547532006132299208327059859 821298009198448812490589789)
          ·
            refine ⟨307986753449418304683971171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 821298009198448812490589789 307986753449418304683971171)
            ·
              refine ⟨461980130174127457025956757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307986753449418304683971171 461980130174127457025956757)
              ·
                refine ⟨21655318601912224548091723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461980130174127457025956757 21655318601912224548091723)
                ·
                  refine ⟨32482977902868336822137585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21655318601912224548091723 32482977902868336822137585)
                  ·
                    refine ⟨24362233427151252616603189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32482977902868336822137585 24362233427151252616603189)
                    ·
                      refine ⟨2283959383795429932806549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24362233427151252616603189 2283959383795429932806549)
                      ·
                        rfl

theorem cell23_4447995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_4447995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4447995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4447995 prefixEnd_4447995 := by exact prefixLift 4447995
  have htrace : WordTrace (prefixWord ++ tailWord_4447995) baseStart_4447995 baseEnd_4447995 := by
    simpa [prefixWord, tailWord_4447995, baseEnd_4447995] using wordTrace_append hprefix tailTrace_4447995
  have hstable : (prefixWord ++ tailWord_4447995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447995).length < 2 ^ (prefixWord ++ tailWord_4447995).sum := by decide
  have hdescent : baseEnd_4447995 < baseStart_4447995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448025 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_4448025 : Nat := 118140960795 + 4448025 * 2 ^ 59
def prefixEnd_4448025 : Nat := 4983230072969 + 3 ^ 40 * 4448025 * 2
def baseEnd_4448025 : Nat := 2283974788215064815431411

theorem tailTrace_4448025 : CollatzResearch.WordTrace tailWord_4448025 prefixEnd_4448025 2283974788215064815431411 := by
  unfold tailWord_4448025
  simp only [CollatzResearch.WordTrace]
  refine ⟨162232799710572562035313529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108155199807048374690209019 162232799710572562035313529)
  ·
    refine ⟨121674599782929421526485147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162232799710572562035313529 121674599782929421526485147)
    ·
      refine ⟨182511899674394132289727721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121674599782929421526485147 182511899674394132289727721)
      ·
        refine ⟨136883924755795599217295791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182511899674394132289727721 136883924755795599217295791)
        ·
          refine ⟨205325887133693398825943687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136883924755795599217295791 205325887133693398825943687)
          ·
            refine ⟨307988830700540098238915531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205325887133693398825943687 307988830700540098238915531)
            ·
              refine ⟨461983246050810147358373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307988830700540098238915531 461983246050810147358373297)
              ·
                refine ⟨346487434538107610518779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461983246050810147358373297 346487434538107610518779973)
                ·
                  refine ⟨64966393975895176972271245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346487434538107610518779973 64966393975895176972271245)
                  ·
                    refine ⟨24362397740960691364601717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64966393975895176972271245 24362397740960691364601717)
                    ·
                      refine ⟨2283974788215064815431411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24362397740960691364601717 2283974788215064815431411)
                      ·
                        rfl

theorem cell23_4448025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_4448025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448025 prefixEnd_4448025 := by exact prefixLift 4448025
  have htrace : WordTrace (prefixWord ++ tailWord_4448025) baseStart_4448025 baseEnd_4448025 := by
    simpa [prefixWord, tailWord_4448025, baseEnd_4448025] using wordTrace_append hprefix tailTrace_4448025
  have hstable : (prefixWord ++ tailWord_4448025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448025).length < 2 ^ (prefixWord ++ tailWord_4448025).sum := by decide
  have hdescent : baseEnd_4448025 < baseStart_4448025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448089 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_4448089 : Nat := 118140960795 + 4448089 * 2 ^ 59
def prefixEnd_4448089 : Nat := 4983230072969 + 3 ^ 40 * 4448089 * 2
def baseEnd_4448089 : Nat := 2284007650976952565031117

theorem tailTrace_4448089 : CollatzResearch.WordTrace tailWord_4448089 prefixEnd_4448089 2284007650976952565031117 := by
  unfold tailWord_4448089
  simp only [CollatzResearch.WordTrace]
  refine ⟨162235133982340700965643321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108156755988227133977095547 162235133982340700965643321)
  ·
    refine ⟨121676350486755525724232491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162235133982340700965643321 121676350486755525724232491)
    ·
      refine ⟨182514525730133288586348737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121676350486755525724232491 182514525730133288586348737)
      ·
        refine ⟨136885894297599966439761553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182514525730133288586348737 136885894297599966439761553)
        ·
          refine ⟨102664420723199974829821165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136885894297599966439761553 102664420723199974829821165)
          ·
            refine ⟨38499157771199990561182937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102664420723199974829821165 38499157771199990561182937)
            ·
              refine ⟨28874368328399992920887203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38499157771199990561182937 28874368328399992920887203)
              ·
                refine ⟨43311552492599989381330805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28874368328399992920887203 43311552492599989381330805)
                ·
                  refine ⟨4060458046181249004499763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43311552492599989381330805 4060458046181249004499763)
                  ·
                    refine ⟨6090687069271873506749645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060458046181249004499763 6090687069271873506749645)
                    ·
                      refine ⟨2284007650976952565031117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090687069271873506749645 2284007650976952565031117)
                      ·
                        rfl

theorem cell23_4448089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_4448089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448089 prefixEnd_4448089 := by exact prefixLift 4448089
  have htrace : WordTrace (prefixWord ++ tailWord_4448089) baseStart_4448089 baseEnd_4448089 := by
    simpa [prefixWord, tailWord_4448089, baseEnd_4448089] using wordTrace_append hprefix tailTrace_4448089
  have hstable : (prefixWord ++ tailWord_4448089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448089).length < 2 ^ (prefixWord ++ tailWord_4448089).sum := by decide
  have hdescent : baseEnd_4448089 < baseStart_4448089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448109 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_4448109 : Nat := 118140960795 + 4448109 * 2 ^ 59
def prefixEnd_4448109 : Nat := 4983230072969 + 3 ^ 40 * 4448109 * 2
def baseEnd_4448109 : Nat := 761339306863347495593675

theorem tailTrace_4448109 : CollatzResearch.WordTrace tailWord_4448109 prefixEnd_4448109 761339306863347495593675 := by
  unfold tailWord_4448109
  simp only [CollatzResearch.WordTrace]
  refine ⟨162235863442268244381371381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108157242294845496254247587 162235863442268244381371381)
  ·
    refine ⟨15209612197712647910753567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162235863442268244381371381 15209612197712647910753567)
    ·
      refine ⟨22814418296568971866130351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15209612197712647910753567 22814418296568971866130351)
      ·
        refine ⟨34221627444853457799195527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22814418296568971866130351 34221627444853457799195527)
        ·
          refine ⟨51332441167280186698793291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34221627444853457799195527 51332441167280186698793291)
          ·
            refine ⟨76998661750920280048189937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51332441167280186698793291 76998661750920280048189937)
            ·
              refine ⟨57748996313190210036142453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76998661750920280048189937 57748996313190210036142453)
              ·
                refine ⟨5413968404361582190888355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57748996313190210036142453 5413968404361582190888355)
                ·
                  refine ⟨8120952606542373286332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5413968404361582190888355 8120952606542373286332533)
                  ·
                    refine ⟨761339306863347495593675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8120952606542373286332533 761339306863347495593675)
                    ·
                      rfl

theorem cell23_4448109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_4448109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448109 prefixEnd_4448109 := by exact prefixLift 4448109
  have htrace : WordTrace (prefixWord ++ tailWord_4448109) baseStart_4448109 baseEnd_4448109 := by
    simpa [prefixWord, tailWord_4448109, baseEnd_4448109] using wordTrace_append hprefix tailTrace_4448109
  have hstable : (prefixWord ++ tailWord_4448109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448109).length < 2 ^ (prefixWord ++ tailWord_4448109).sum := by decide
  have hdescent : baseEnd_4448109 < baseStart_4448109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448126 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4448126 : Nat := 118140960795 + 4448126 * 2 ^ 59
def prefixEnd_4448126 : Nat := 4983230072969 + 3 ^ 40 * 4448126 * 2
def baseEnd_4448126 : Nat := 761342216587056306756149

theorem tailTrace_4448126 : CollatzResearch.WordTrace tailWord_4448126 prefixEnd_4448126 761342216587056306756149 := by
  unfold tailWord_4448126
  simp only [CollatzResearch.WordTrace]
  refine ⟨20279560435400832035592529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108157655655471104189826821 20279560435400832035592529)
  ·
    refine ⟨15209670326550624026694397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20279560435400832035592529 15209670326550624026694397)
    ·
      refine ⟨5703626372456484010010399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15209670326550624026694397 5703626372456484010010399)
      ·
        refine ⟨8555439558684726015015599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703626372456484010010399 8555439558684726015015599)
        ·
          refine ⟨12833159338027089022523399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555439558684726015015599 12833159338027089022523399)
          ·
            refine ⟨19249739007040633533785099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12833159338027089022523399 19249739007040633533785099)
            ·
              refine ⟨28874608510560950300677649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19249739007040633533785099 28874608510560950300677649)
              ·
                refine ⟨21655956382920712725508237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28874608510560950300677649 21655956382920712725508237)
                ·
                  refine ⟨8120983643595267272065589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21655956382920712725508237 8120983643595267272065589)
                  ·
                    refine ⟨761342216587056306756149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8120983643595267272065589 761342216587056306756149)
                    ·
                      rfl

theorem cell23_4448126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4448126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448126 prefixEnd_4448126 := by exact prefixLift 4448126
  have htrace : WordTrace (prefixWord ++ tailWord_4448126) baseStart_4448126 baseEnd_4448126 := by
    simpa [prefixWord, tailWord_4448126, baseEnd_4448126] using wordTrace_append hprefix tailTrace_4448126
  have hstable : (prefixWord ++ tailWord_4448126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448126).length < 2 ^ (prefixWord ++ tailWord_4448126).sum := by decide
  have hdescent : baseEnd_4448126 < baseStart_4448126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448146 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4448146 : Nat := 118140960795 + 4448146 * 2 ^ 59
def prefixEnd_4448146 : Nat := 4983230072969 + 3 ^ 40 * 4448146 * 2
def baseEnd_4448146 : Nat := 2284036919374258842018355

theorem tailTrace_4448146 : CollatzResearch.WordTrace tailWord_4448146 prefixEnd_4448146 2284036919374258842018355 := by
  unfold tailWord_4448146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40559303235783549925117073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108158141962089466466978861 40559303235783549925117073)
  ·
    refine ⟨30419477426837662443837805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40559303235783549925117073 30419477426837662443837805)
    ·
      refine ⟨11407304035064123416439177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30419477426837662443837805 11407304035064123416439177)
      ·
        refine ⟨8555478026298092562329383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11407304035064123416439177 8555478026298092562329383)
        ·
          refine ⟨12833217039447138843494075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555478026298092562329383 12833217039447138843494075)
          ·
            refine ⟨19249825559170708265241113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12833217039447138843494075 19249825559170708265241113)
            ·
              refine ⟨14437369169378031198930835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19249825559170708265241113 14437369169378031198930835)
              ·
                refine ⟨21656053754067046798396253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14437369169378031198930835 21656053754067046798396253)
                ·
                  refine ⟨8121020157775142549398595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21656053754067046798396253 8121020157775142549398595)
                  ·
                    refine ⟨12181530236662713824097893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8121020157775142549398595 12181530236662713824097893)
                    ·
                      refine ⟨2284036919374258842018355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12181530236662713824097893 2284036919374258842018355)
                      ·
                        rfl

theorem cell23_4448146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4448146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448146 prefixEnd_4448146 := by exact prefixLift 4448146
  have htrace : WordTrace (prefixWord ++ tailWord_4448146) baseStart_4448146 baseEnd_4448146 := by
    simpa [prefixWord, tailWord_4448146, baseEnd_4448146] using wordTrace_append hprefix tailTrace_4448146
  have hstable : (prefixWord ++ tailWord_4448146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448146).length < 2 ^ (prefixWord ++ tailWord_4448146).sum := by decide
  have hdescent : baseEnd_4448146 < baseStart_4448146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448149 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_4448149 : Nat := 118140960795 + 4448149 * 2 ^ 59
def prefixEnd_4448149 : Nat := 4983230072969 + 3 ^ 40 * 4448149 * 2
def baseEnd_4448149 : Nat := 2284038459816222330280841

theorem tailTrace_4448149 : CollatzResearch.WordTrace tailWord_4448149 prefixEnd_4448149 2284038459816222330280841 := by
  unfold tailWord_4448149
  simp only [CollatzResearch.WordTrace]
  refine ⟨162237322362123331212827501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108158214908082220808551667 162237322362123331212827501)
  ·
    refine ⟨60838995885796249204810313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162237322362123331212827501 60838995885796249204810313)
    ·
      refine ⟨45629246914347186903607735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60838995885796249204810313 45629246914347186903607735)
      ·
        refine ⟨68443870371520780355411603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45629246914347186903607735 68443870371520780355411603)
        ·
          refine ⟨102665805557281170533117405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68443870371520780355411603 102665805557281170533117405)
          ·
            refine ⟨38499677083980438949919027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102665805557281170533117405 38499677083980438949919027)
            ·
              refine ⟨57749515625970658424878541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38499677083980438949919027 57749515625970658424878541)
              ·
                refine ⟨21656068359738996909329453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57749515625970658424878541 21656068359738996909329453)
                ·
                  refine ⟨8121025634902123840998545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21656068359738996909329453 8121025634902123840998545)
                  ·
                    refine ⟨6090769226176592880748909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8121025634902123840998545 6090769226176592880748909)
                    ·
                      refine ⟨2284038459816222330280841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090769226176592880748909 2284038459816222330280841)
                      ·
                        rfl

theorem cell23_4448149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_4448149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448149 prefixEnd_4448149 := by exact prefixLift 4448149
  have htrace : WordTrace (prefixWord ++ tailWord_4448149) baseStart_4448149 baseEnd_4448149 := by
    simpa [prefixWord, tailWord_4448149, baseEnd_4448149] using wordTrace_append hprefix tailTrace_4448149
  have hstable : (prefixWord ++ tailWord_4448149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448149).length < 2 ^ (prefixWord ++ tailWord_4448149).sum := by decide
  have hdescent : baseEnd_4448149 < baseStart_4448149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448220 : List Nat := [2, 2, 6, 1, 2, 1, 9]
def baseStart_4448220 : Nat := 118140960795 + 4448220 * 2 ^ 59
def prefixEnd_4448220 : Nat := 4983230072969 + 3 ^ 40 * 4448220 * 2
def baseEnd_4448220 : Nat := 28198455764724587067815

theorem tailTrace_4448220 : CollatzResearch.WordTrace tailWord_4448220 prefixEnd_4448220 28198455764724587067815 := by
  unfold tailWord_4448220
  simp only [CollatzResearch.WordTrace]
  refine ⟨81119955972433055169331057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108159941296577406892441409 81119955972433055169331057)
  ·
    refine ⟨60839966979324791376998293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81119955972433055169331057 60839966979324791376998293)
    ·
      refine ⟨2851873452155849595796795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60839966979324791376998293 2851873452155849595796795)
      ·
        refine ⟨4277810178233774393695193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851873452155849595796795 4277810178233774393695193)
        ·
          refine ⟨3208357633675330795271395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277810178233774393695193 3208357633675330795271395)
          ·
            refine ⟨4812536450512996192907093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208357633675330795271395 4812536450512996192907093)
            ·
              refine ⟨28198455764724587067815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4812536450512996192907093 28198455764724587067815)
              ·
                rfl

theorem cell23_4448220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 9].length) (baseStart_4448220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448220 prefixEnd_4448220 := by exact prefixLift 4448220
  have htrace : WordTrace (prefixWord ++ tailWord_4448220) baseStart_4448220 baseEnd_4448220 := by
    simpa [prefixWord, tailWord_4448220, baseEnd_4448220] using wordTrace_append hprefix tailTrace_4448220
  have hstable : (prefixWord ++ tailWord_4448220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448220).length < 2 ^ (prefixWord ++ tailWord_4448220).sum := by decide
  have hdescent : baseEnd_4448220 < baseStart_4448220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448223 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 1, 3, 2]
def baseStart_4448223 : Nat := 118140960795 + 4448223 * 2 ^ 59
def prefixEnd_4448223 : Nat := 4983230072969 + 3 ^ 40 * 4448223 * 2
def baseEnd_4448223 : Nat := 2284076457384655040755501

theorem tailTrace_4448223 : CollatzResearch.WordTrace tailWord_4448223 prefixEnd_4448223 2284076457384655040755501 := by
  unfold tailWord_4448223
  simp only [CollatzResearch.WordTrace]
  refine ⟨162240021363855241851021323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108160014242570161234014215 162240021363855241851021323)
  ·
    refine ⟨243360032045782862776531985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162240021363855241851021323 243360032045782862776531985)
    ·
      refine ⟨182520024034337147082398989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243360032045782862776531985 182520024034337147082398989)
      ·
        refine ⟨68445009012876430155899621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182520024034337147082398989 68445009012876430155899621)
        ·
          refine ⟨12833439189914330654231179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68445009012876430155899621 12833439189914330654231179)
          ·
            refine ⟨19250158784871495981346769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12833439189914330654231179 19250158784871495981346769)
            ·
              refine ⟨14437619088653621986010077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19250158784871495981346769 14437619088653621986010077)
              ·
                refine ⟨5414107158245108244753779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14437619088653621986010077 5414107158245108244753779)
                ·
                  refine ⟨8121160737367662367130669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414107158245108244753779 8121160737367662367130669)
                  ·
                    refine ⟨3045435276512873387674001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8121160737367662367130669 3045435276512873387674001)
                    ·
                      refine ⟨2284076457384655040755501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045435276512873387674001 2284076457384655040755501)
                      ·
                        rfl

theorem cell23_4448223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_4448223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448223 prefixEnd_4448223 := by exact prefixLift 4448223
  have htrace : WordTrace (prefixWord ++ tailWord_4448223) baseStart_4448223 baseEnd_4448223 := by
    simpa [prefixWord, tailWord_4448223, baseEnd_4448223] using wordTrace_append hprefix tailTrace_4448223
  have hstable : (prefixWord ++ tailWord_4448223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448223).length < 2 ^ (prefixWord ++ tailWord_4448223).sum := by decide
  have hdescent : baseEnd_4448223 < baseStart_4448223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448239 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_4448239 : Nat := 118140960795 + 4448239 * 2 ^ 59
def prefixEnd_4448239 : Nat := 4983230072969 + 3 ^ 40 * 4448239 * 2
def baseEnd_4448239 : Nat := 2284084673075126978155427

theorem tailTrace_4448239 : CollatzResearch.WordTrace tailWord_4448239 prefixEnd_4448239 2284084673075126978155427 := by
  unfold tailWord_4448239
  simp only [CollatzResearch.WordTrace]
  refine ⟨162240604931797276583603771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108160403287864851055735847 162240604931797276583603771)
  ·
    refine ⟨243360907397695914875405657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162240604931797276583603771 243360907397695914875405657)
    ·
      refine ⟨182520680548271936156554243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243360907397695914875405657 182520680548271936156554243)
      ·
        refine ⟨273781020822407904234831365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182520680548271936156554243 273781020822407904234831365)
        ·
          refine ⟨51333941404201482044030881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273781020822407904234831365 51333941404201482044030881)
          ·
            refine ⟨38500456053151111533023161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51333941404201482044030881 38500456053151111533023161)
            ·
              refine ⟨28875342039863333649767371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38500456053151111533023161 28875342039863333649767371)
              ·
                refine ⟨43313013059795000474651057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28875342039863333649767371 43313013059795000474651057)
                ·
                  refine ⟨32484759794846250355988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43313013059795000474651057 32484759794846250355988293)
                  ·
                    refine ⟨6090892461533671941747805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32484759794846250355988293 6090892461533671941747805)
                    ·
                      refine ⟨2284084673075126978155427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6090892461533671941747805 2284084673075126978155427)
                      ·
                        rfl

theorem cell23_4448239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_4448239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448239 prefixEnd_4448239 := by exact prefixLift 4448239
  have htrace : WordTrace (prefixWord ++ tailWord_4448239) baseStart_4448239 baseEnd_4448239 := by
    simpa [prefixWord, tailWord_4448239, baseEnd_4448239] using wordTrace_append hprefix tailTrace_4448239
  have hstable : (prefixWord ++ tailWord_4448239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448239).length < 2 ^ (prefixWord ++ tailWord_4448239).sum := by decide
  have hdescent : baseEnd_4448239 < baseStart_4448239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448293 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 5]
def baseStart_4448293 : Nat := 118140960795 + 4448293 * 2 ^ 59
def prefixEnd_4448293 : Nat := 4983230072969 + 3 ^ 40 * 4448293 * 2
def baseEnd_4448293 : Nat := 253790266781163307431131

theorem tailTrace_4448293 : CollatzResearch.WordTrace tailWord_4448293 prefixEnd_4448293 253790266781163307431131 := by
  unfold tailWord_4448293
  simp only [CollatzResearch.WordTrace]
  refine ⟨162242574473601643806069533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108161716315734429204046355 162242574473601643806069533)
  ·
    refine ⟨60840965427600616427276075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162242574473601643806069533 60840965427600616427276075)
    ·
      refine ⟨91261448141400924640914113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60840965427600616427276075 91261448141400924640914113)
      ·
        refine ⟨68446086106050693480685585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91261448141400924640914113 68446086106050693480685585)
        ·
          refine ⟨51334564579538020110514189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68446086106050693480685585 51334564579538020110514189)
          ·
            refine ⟨19250461717326757541442821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51334564579538020110514189 19250461717326757541442821)
            ·
              refine ⟨3609461571998767039020529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19250461717326757541442821 3609461571998767039020529)
              ·
                refine ⟨2707096178999075279265397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609461571998767039020529 2707096178999075279265397)
                ·
                  refine ⟨253790266781163307431131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2707096178999075279265397 253790266781163307431131)
                  ·
                    rfl

theorem cell23_4448293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_4448293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448293 prefixEnd_4448293 := by exact prefixLift 4448293
  have htrace : WordTrace (prefixWord ++ tailWord_4448293) baseStart_4448293 baseEnd_4448293 := by
    simpa [prefixWord, tailWord_4448293, baseEnd_4448293] using wordTrace_append hprefix tailTrace_4448293
  have hstable : (prefixWord ++ tailWord_4448293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448293).length < 2 ^ (prefixWord ++ tailWord_4448293).sum := by decide
  have hdescent : baseEnd_4448293 < baseStart_4448293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448346 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_4448346 : Nat := 118140960795 + 4448346 * 2 ^ 59
def prefixEnd_4448346 : Nat := 4983230072969 + 3 ^ 40 * 4448346 * 2
def baseEnd_4448346 : Nat := 2284139615505158059517435

theorem tailTrace_4448346 : CollatzResearch.WordTrace tailWord_4448346 prefixEnd_4448346 2284139615505158059517435 := by
  unfold tailWord_4448346
  simp only [CollatzResearch.WordTrace]
  refine ⟨40561126885602408464437223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108163005028273089238499261 40561126885602408464437223)
  ·
    refine ⟨60841690328403612696655835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40561126885602408464437223 60841690328403612696655835)
    ·
      refine ⟨91262535492605419044983753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60841690328403612696655835 91262535492605419044983753)
      ·
        refine ⟨68446901619454064283737815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91262535492605419044983753 68446901619454064283737815)
        ·
          refine ⟨102670352429181096425606723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68446901619454064283737815 102670352429181096425606723)
          ·
            refine ⟨154005528643771644638410085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102670352429181096425606723 154005528643771644638410085)
            ·
              refine ⟨28876036620707183369701891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154005528643771644638410085 28876036620707183369701891)
              ·
                refine ⟨43314054931060775054552837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28876036620707183369701891 43314054931060775054552837)
                ·
                  refine ⟨8121385299573895322728657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43314054931060775054552837 8121385299573895322728657)
                  ·
                    refine ⟨6091038974680421492046493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8121385299573895322728657 6091038974680421492046493)
                    ·
                      refine ⟨2284139615505158059517435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091038974680421492046493 2284139615505158059517435)
                      ·
                        rfl

theorem cell23_4448346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_4448346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448346 prefixEnd_4448346 := by exact prefixLift 4448346
  have htrace : WordTrace (prefixWord ++ tailWord_4448346) baseStart_4448346 baseEnd_4448346 := by
    simpa [prefixWord, tailWord_4448346, baseEnd_4448346] using wordTrace_append hprefix tailTrace_4448346
  have hstable : (prefixWord ++ tailWord_4448346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448346).length < 2 ^ (prefixWord ++ tailWord_4448346).sum := by decide
  have hdescent : baseEnd_4448346 < baseStart_4448346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448369 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_4448369 : Nat := 118140960795 + 4448369 * 2 ^ 59
def prefixEnd_4448369 : Nat := 4983230072969 + 3 ^ 40 * 4448369 * 2
def baseEnd_4448369 : Nat := 2284151425560211469529829

theorem tailTrace_4448369 : CollatzResearch.WordTrace tailWord_4448369 prefixEnd_4448369 2284151425560211469529829 := by
  unfold tailWord_4448369
  simp only [CollatzResearch.WordTrace]
  refine ⟨162245346421326308785836161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108163564280884205857224107 162245346421326308785836161)
  ·
    refine ⟨121684009815994731589377121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162245346421326308785836161 121684009815994731589377121)
    ·
      refine ⟨91263007361996048692032841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121684009815994731589377121 91263007361996048692032841)
      ·
        refine ⟨68447255521497036519024631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91263007361996048692032841 68447255521497036519024631)
        ·
          refine ⟨102670883282245554778536947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68447255521497036519024631 102670883282245554778536947)
          ·
            refine ⟨154006324923368332167805421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102670883282245554778536947 154006324923368332167805421)
            ·
              refine ⟨57752371846263124562927033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154006324923368332167805421 57752371846263124562927033)
              ·
                refine ⟨43314278884697343422195275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57752371846263124562927033 43314278884697343422195275)
                ·
                  refine ⟨64971418327046015133292913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43314278884697343422195275 64971418327046015133292913)
                  ·
                    refine ⟨48728563745284511349969685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64971418327046015133292913 48728563745284511349969685)
                    ·
                      refine ⟨2284151425560211469529829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48728563745284511349969685 2284151425560211469529829)
                      ·
                        rfl

theorem cell23_4448369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_4448369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448369 prefixEnd_4448369 := by exact prefixLift 4448369
  have htrace : WordTrace (prefixWord ++ tailWord_4448369) baseStart_4448369 baseEnd_4448369 := by
    simpa [prefixWord, tailWord_4448369, baseEnd_4448369] using wordTrace_append hprefix tailTrace_4448369
  have hstable : (prefixWord ++ tailWord_4448369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448369).length < 2 ^ (prefixWord ++ tailWord_4448369).sum := by decide
  have hdescent : baseEnd_4448369 < baseStart_4448369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448404 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_4448404 : Nat := 118140960795 + 4448404 * 2 ^ 59
def prefixEnd_4448404 : Nat := 4983230072969 + 3 ^ 40 * 4448404 * 2
def baseEnd_4448404 : Nat := 761389799127706277530723

theorem tailTrace_4448404 : CollatzResearch.WordTrace tailWord_4448404 prefixEnd_4448404 761389799127706277530723 := by
  unfold tailWord_4448404
  simp only [CollatzResearch.WordTrace]
  refine ⟨81123311488099754881680133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108164415317466339842240177 81123311488099754881680133)
  ·
    refine ⟨15210620904018704040315025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81123311488099754881680133 15210620904018704040315025)
    ·
      refine ⟨11407965678014028030236269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15210620904018704040315025 11407965678014028030236269)
      ·
        refine ⟨4277987129255260511338601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11407965678014028030236269 4277987129255260511338601)
        ·
          refine ⟨3208490346941445383503951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277987129255260511338601 3208490346941445383503951)
          ·
            refine ⟨4812735520412168075255927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208490346941445383503951 4812735520412168075255927)
            ·
              refine ⟨7219103280618252112883891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812735520412168075255927 7219103280618252112883891)
              ·
                refine ⟨10828654920927378169325837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7219103280618252112883891 10828654920927378169325837)
                ·
                  refine ⟨4060745595347766813497189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10828654920927378169325837 4060745595347766813497189)
                  ·
                    refine ⟨761389799127706277530723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060745595347766813497189 761389799127706277530723)
                    ·
                      rfl

theorem cell23_4448404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_4448404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448404 prefixEnd_4448404 := by exact prefixLift 4448404
  have htrace : WordTrace (prefixWord ++ tailWord_4448404) baseStart_4448404 baseEnd_4448404 := by
    simpa [prefixWord, tailWord_4448404, baseEnd_4448404] using wordTrace_append hprefix tailTrace_4448404
  have hstable : (prefixWord ++ tailWord_4448404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448404).length < 2 ^ (prefixWord ++ tailWord_4448404).sum := by decide
  have hdescent : baseEnd_4448404 < baseStart_4448404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448453 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_4448453 : Nat := 118140960795 + 4448453 * 2 ^ 59
def prefixEnd_4448453 : Nat := 4983230072969 + 3 ^ 40 * 4448453 * 2
def baseEnd_4448453 : Nat := 2284194557935189140879443

theorem tailTrace_4448453 : CollatzResearch.WordTrace tailWord_4448453 prefixEnd_4448453 2284194557935189140879443 := by
  unfold tailWord_4448453
  simp only [CollatzResearch.WordTrace]
  refine ⟨162248410153021991131894013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108165606768681327421262675 162248410153021991131894013)
  ·
    refine ⟨60843153807383246674460255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162248410153021991131894013 60843153807383246674460255)
    ·
      refine ⟨91264730711074870011690383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60843153807383246674460255 91264730711074870011690383)
      ·
        refine ⟨136897096066612305017535575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91264730711074870011690383 136897096066612305017535575)
        ·
          refine ⟨205345644099918457526303363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136897096066612305017535575 205345644099918457526303363)
          ·
            refine ⟨308018466149877686289455045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205345644099918457526303363 308018466149877686289455045)
            ·
              refine ⟨57753462403102066179272821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308018466149877686289455045 57753462403102066179272821)
              ·
                refine ⟨5414387100290818704306827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57753462403102066179272821 5414387100290818704306827)
                ·
                  refine ⟨8121580650436228056460241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414387100290818704306827 8121580650436228056460241)
                  ·
                    refine ⟨6091185487827171042345181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8121580650436228056460241 6091185487827171042345181)
                    ·
                      refine ⟨2284194557935189140879443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091185487827171042345181 2284194557935189140879443)
                      ·
                        rfl

theorem cell23_4448453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_4448453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448453 prefixEnd_4448453 := by exact prefixLift 4448453
  have htrace : WordTrace (prefixWord ++ tailWord_4448453) baseStart_4448453 baseEnd_4448453 := by
    simpa [prefixWord, tailWord_4448453, baseEnd_4448453] using wordTrace_append hprefix tailTrace_4448453
  have hstable : (prefixWord ++ tailWord_4448453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448453).length < 2 ^ (prefixWord ++ tailWord_4448453).sum := by decide
  have hdescent : baseEnd_4448453 < baseStart_4448453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448576 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_4448576 : Nat := 118140960795 + 4448576 * 2 ^ 59
def prefixEnd_4448576 : Nat := 4983230072969 + 3 ^ 40 * 4448576 * 2
def baseEnd_4448576 : Nat := 761419238685230719880459

theorem tailTrace_4448576 : CollatzResearch.WordTrace tailWord_4448576 prefixEnd_4448576 761419238685230719880459 := by
  unfold tailWord_4448576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81126448165788191569310791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108168597554384255425747721 81126448165788191569310791)
  ·
    refine ⟨121689672248682287353966187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81126448165788191569310791 121689672248682287353966187)
    ·
      refine ⟨182534508373023431030949281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121689672248682287353966187 182534508373023431030949281)
      ·
        refine ⟨136900881279767573273211961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182534508373023431030949281 136900881279767573273211961)
        ·
          refine ⟨102675660959825679954908971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136900881279767573273211961 102675660959825679954908971)
          ·
            refine ⟨154013491439738519932363457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102675660959825679954908971 154013491439738519932363457)
            ·
              refine ⟨115510118579803889949272593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154013491439738519932363457 115510118579803889949272593)
              ·
                refine ⟨86632588934852917461954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115510118579803889949272593 86632588934852917461954445)
                ·
                  refine ⟨32487220850569844048232917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86632588934852917461954445 32487220850569844048232917)
                  ·
                    refine ⟨761419238685230719880459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32487220850569844048232917 761419238685230719880459)
                    ·
                      rfl

theorem cell23_4448576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_4448576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448576 prefixEnd_4448576 := by exact prefixLift 4448576
  have htrace : WordTrace (prefixWord ++ tailWord_4448576) baseStart_4448576 baseEnd_4448576 := by
    simpa [prefixWord, tailWord_4448576, baseEnd_4448576] using wordTrace_append hprefix tailTrace_4448576
  have hstable : (prefixWord ++ tailWord_4448576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448576).length < 2 ^ (prefixWord ++ tailWord_4448576).sum := by decide
  have hdescent : baseEnd_4448576 < baseStart_4448576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448610 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4448610 : Nat := 118140960795 + 4448610 * 2 ^ 59
def prefixEnd_4448610 : Nat := 4983230072969 + 3 ^ 40 * 4448610 * 2
def baseEnd_4448610 : Nat := 761425058132648342205407

theorem tailTrace_4448610 : CollatzResearch.WordTrace tailWord_4448610 prefixEnd_4448610 761425058132648342205407 := by
  unfold tailWord_4448610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40563534103363301736339821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108169424275635471296906189 40563534103363301736339821)
  ·
    refine ⟨15211325288761238151127433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40563534103363301736339821 15211325288761238151127433)
    ·
      refine ⟨11408493966570928613345575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15211325288761238151127433 11408493966570928613345575)
      ·
        refine ⟨17112740949856392920018363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11408493966570928613345575 17112740949856392920018363)
        ·
          refine ⟨25669111424784589380027545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17112740949856392920018363 25669111424784589380027545)
          ·
            refine ⟨19251833568588442035020659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25669111424784589380027545 19251833568588442035020659)
            ·
              refine ⟨28877750352882663052530989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19251833568588442035020659 28877750352882663052530989)
              ·
                refine ⟨10829156382330998644699121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28877750352882663052530989 10829156382330998644699121)
                ·
                  refine ⟨8121867286748248983524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10829156382330998644699121 8121867286748248983524341)
                  ·
                    refine ⟨761425058132648342205407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8121867286748248983524341 761425058132648342205407)
                    ·
                      rfl

theorem cell23_4448610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4448610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448610 prefixEnd_4448610 := by exact prefixLift 4448610
  have htrace : WordTrace (prefixWord ++ tailWord_4448610) baseStart_4448610 baseEnd_4448610 := by
    simpa [prefixWord, tailWord_4448610, baseEnd_4448610] using wordTrace_append hprefix tailTrace_4448610
  have hstable : (prefixWord ++ tailWord_4448610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448610).length < 2 ^ (prefixWord ++ tailWord_4448610).sum := by decide
  have hdescent : baseEnd_4448610 < baseStart_4448610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448623 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 7, 4]
def baseStart_4448623 : Nat := 118140960795 + 4448623 * 2 ^ 59
def prefixEnd_4448623 : Nat := 4983230072969 + 3 ^ 40 * 4448623 * 2
def baseEnd_4448623 : Nat := 761427283215484491917887

theorem tailTrace_4448623 : CollatzResearch.WordTrace tailWord_4448623 prefixEnd_4448623 761427283215484491917887 := by
  unfold tailWord_4448623
  simp only [CollatzResearch.WordTrace]
  refine ⟨162254610562406110165582523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108169740374937406777055015 162254610562406110165582523)
  ·
    refine ⟨243381915843609165248373785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162254610562406110165582523 243381915843609165248373785)
    ·
      refine ⟨182536436882706873936280339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243381915843609165248373785 182536436882706873936280339)
      ·
        refine ⟨273804655324060310904420509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182536436882706873936280339 273804655324060310904420509)
        ·
          refine ⟨102676745746522616589157691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273804655324060310904420509 102676745746522616589157691)
          ·
            refine ⟨154015118619783924883736537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102676745746522616589157691 154015118619783924883736537)
            ·
              refine ⟨115511338964837943662802403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154015118619783924883736537 115511338964837943662802403)
              ·
                refine ⟨173267008447256915494203605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115511338964837943662802403 173267008447256915494203605)
                ·
                  refine ⟨4060945510482583956895397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173267008447256915494203605 4060945510482583956895397)
                  ·
                    refine ⟨761427283215484491917887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060945510482583956895397 761427283215484491917887)
                    ·
                      rfl

theorem cell23_4448623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_4448623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448623 prefixEnd_4448623 := by exact prefixLift 4448623
  have htrace : WordTrace (prefixWord ++ tailWord_4448623) baseStart_4448623 baseEnd_4448623 := by
    simpa [prefixWord, tailWord_4448623, baseEnd_4448623] using wordTrace_append hprefix tailTrace_4448623
  have hstable : (prefixWord ++ tailWord_4448623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448623).length < 2 ^ (prefixWord ++ tailWord_4448623).sum := by decide
  have hdescent : baseEnd_4448623 < baseStart_4448623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448633 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4448633 : Nat := 118140960795 + 4448633 * 2 ^ 59
def prefixEnd_4448633 : Nat := 4983230072969 + 3 ^ 40 * 4448633 * 2
def baseEnd_4448633 : Nat := 2284286984452998436628615

theorem tailTrace_4448633 : CollatzResearch.WordTrace tailWord_4448633 prefixEnd_4448633 2284286984452998436628615 := by
  unfold tailWord_4448633
  simp only [CollatzResearch.WordTrace]
  refine ⟨162254975292369881873446553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108169983528246587915631035 162254975292369881873446553)
  ·
    refine ⟨121691231469277411405084915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162254975292369881873446553 121691231469277411405084915)
    ·
      refine ⟨182536847203916117107627373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121691231469277411405084915 182536847203916117107627373)
      ·
        refine ⟨68451317701468543915360265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182536847203916117107627373 68451317701468543915360265)
        ·
          refine ⟨51338488276101407936520199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68451317701468543915360265 51338488276101407936520199)
          ·
            refine ⟨77007732414152111904780299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51338488276101407936520199 77007732414152111904780299)
            ·
              refine ⟨115511598621228167857170449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77007732414152111904780299 115511598621228167857170449)
              ·
                refine ⟨86633698965921125892877837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115511598621228167857170449 86633698965921125892877837)
                ·
                  refine ⟨32487637112220422209829189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86633698965921125892877837 32487637112220422209829189)
                  ·
                    refine ⟨6091431958541329164342973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32487637112220422209829189 6091431958541329164342973)
                    ·
                      refine ⟨2284286984452998436628615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091431958541329164342973 2284286984452998436628615)
                      ·
                        rfl

theorem cell23_4448633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4448633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448633 prefixEnd_4448633 := by exact prefixLift 4448633
  have htrace : WordTrace (prefixWord ++ tailWord_4448633) baseStart_4448633 baseEnd_4448633 := by
    simpa [prefixWord, tailWord_4448633, baseEnd_4448633] using wordTrace_append hprefix tailTrace_4448633
  have hstable : (prefixWord ++ tailWord_4448633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448633).length < 2 ^ (prefixWord ++ tailWord_4448633).sum := by decide
  have hdescent : baseEnd_4448633 < baseStart_4448633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448674 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4448674 : Nat := 118140960795 + 4448674 * 2 ^ 59
def prefixEnd_4448674 : Nat := 4983230072969 + 3 ^ 40 * 4448674 * 2
def baseEnd_4448674 : Nat := 761436012386610925405309

theorem tailTrace_4448674 : CollatzResearch.WordTrace tailWord_4448674 prefixEnd_4448674 761436012386610925405309 := by
  unfold tailWord_4448674
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564117671305336468922269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108170980456814230583792717 40564117671305336468922269)
  ·
    refine ⟨15211544126739501175845851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40564117671305336468922269 15211544126739501175845851)
    ·
      refine ⟨22817316190109251763768777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15211544126739501175845851 22817316190109251763768777)
      ·
        refine ⟨17112987142581938822826583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22817316190109251763768777 17112987142581938822826583)
        ·
          refine ⟨25669480713872908234239875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17112987142581938822826583 25669480713872908234239875)
          ·
            refine ⟨38504221070809362351359813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25669480713872908234239875 38504221070809362351359813)
            ·
              refine ⟨7219541450776755440879965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38504221070809362351359813 7219541450776755440879965)
              ·
                refine ⟨2707328044041283290329987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7219541450776755440879965 2707328044041283290329987)
                ·
                  refine ⟨4060992066061924935494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707328044041283290329987 4060992066061924935494981)
                  ·
                    refine ⟨761436012386610925405309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060992066061924935494981 761436012386610925405309)
                    ·
                      rfl

theorem cell23_4448674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4448674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448674 prefixEnd_4448674 := by exact prefixLift 4448674
  have htrace : WordTrace (prefixWord ++ tailWord_4448674) baseStart_4448674 baseEnd_4448674 := by
    simpa [prefixWord, tailWord_4448674, baseEnd_4448674] using wordTrace_append hprefix tailTrace_4448674
  have hstable : (prefixWord ++ tailWord_4448674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448674).length < 2 ^ (prefixWord ++ tailWord_4448674).sum := by decide
  have hdescent : baseEnd_4448674 < baseStart_4448674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448697 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4448697 : Nat := 118140960795 + 4448697 * 2 ^ 59
def prefixEnd_4448697 : Nat := 4983230072969 + 3 ^ 40 * 4448697 * 2
def baseEnd_4448697 : Nat := 2284319847214886186228321

theorem tailTrace_4448697 : CollatzResearch.WordTrace tailWord_4448697 prefixEnd_4448697 2284319847214886186228321 := by
  unfold tailWord_4448697
  simp only [CollatzResearch.WordTrace]
  refine ⟨162257309564138020803776345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108171539709425347202517563 162257309564138020803776345)
  ·
    refine ⟨121692982173103515602832259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162257309564138020803776345 121692982173103515602832259)
    ·
      refine ⟨182539473259655273404248389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121692982173103515602832259 182539473259655273404248389)
      ·
        refine ⟨34226151236185363763296573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182539473259655273404248389 34226151236185363763296573)
        ·
          refine ⟨12834806713569511411236215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34226151236185363763296573 12834806713569511411236215)
          ·
            refine ⟨19252210070354267116854323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12834806713569511411236215 19252210070354267116854323)
            ·
              refine ⟨28878315105531400675281485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19252210070354267116854323 28878315105531400675281485)
              ·
                refine ⟨10829368164574275253230557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28878315105531400675281485 10829368164574275253230557)
                ·
                  refine ⟨4061013061715353219961459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10829368164574275253230557 4061013061715353219961459)
                  ·
                    refine ⟨6091519592573029829942189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061013061715353219961459 6091519592573029829942189)
                    ·
                      refine ⟨2284319847214886186228321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091519592573029829942189 2284319847214886186228321)
                      ·
                        rfl

theorem cell23_4448697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4448697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448697 prefixEnd_4448697 := by exact prefixLift 4448697
  have htrace : WordTrace (prefixWord ++ tailWord_4448697) baseStart_4448697 baseEnd_4448697 := by
    simpa [prefixWord, tailWord_4448697, baseEnd_4448697] using wordTrace_append hprefix tailTrace_4448697
  have hstable : (prefixWord ++ tailWord_4448697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448697).length < 2 ^ (prefixWord ++ tailWord_4448697).sum := by decide
  have hdescent : baseEnd_4448697 < baseStart_4448697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448730 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_4448730 : Nat := 118140960795 + 4448730 * 2 ^ 59
def prefixEnd_4448730 : Nat := 4983230072969 + 3 ^ 40 * 4448730 * 2
def baseEnd_4448730 : Nat := 761445597358828185705223

theorem tailTrace_4448730 : CollatzResearch.WordTrace tailWord_4448730 prefixEnd_4448730 761445597358828185705223 := by
  unfold tailWord_4448730
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564628293254616859931911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108172342115345644959818429 40564628293254616859931911)
  ·
    refine ⟨60846942439881925289897867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40564628293254616859931911 60846942439881925289897867)
    ·
      refine ⟨91270413659822887934846801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60846942439881925289897867 91270413659822887934846801)
      ·
        refine ⟨68452810244867165951135101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91270413659822887934846801 68452810244867165951135101)
        ·
          refine ⟨25669803841825187231675663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68452810244867165951135101 25669803841825187231675663)
          ·
            refine ⟨38504705762737780847513495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25669803841825187231675663 38504705762737780847513495)
            ·
              refine ⟨57757058644106671271270243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38504705762737780847513495 57757058644106671271270243)
              ·
                refine ⟨86635587966160006906905365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57757058644106671271270243 86635587966160006906905365)
                ·
                  refine ⟨4061043185913750323761189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86635587966160006906905365 4061043185913750323761189)
                  ·
                    refine ⟨761445597358828185705223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061043185913750323761189 761445597358828185705223)
                    ·
                      rfl

theorem cell23_4448730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_4448730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448730 prefixEnd_4448730 := by exact prefixLift 4448730
  have htrace : WordTrace (prefixWord ++ tailWord_4448730) baseStart_4448730 baseEnd_4448730 := by
    simpa [prefixWord, tailWord_4448730, baseEnd_4448730] using wordTrace_append hprefix tailTrace_4448730
  have hstable : (prefixWord ++ tailWord_4448730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448730).length < 2 ^ (prefixWord ++ tailWord_4448730).sum := by decide
  have hdescent : baseEnd_4448730 < baseStart_4448730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448740 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_4448740 : Nat := 118140960795 + 4448740 * 2 ^ 59
def prefixEnd_4448740 : Nat := 4983230072969 + 3 ^ 40 * 4448740 * 2
def baseEnd_4448740 : Nat := 2284341926883029517990623

theorem tailTrace_4448740 : CollatzResearch.WordTrace tailWord_4448740 prefixEnd_4448740 2284341926883029517990623 := by
  unfold tailWord_4448740
  simp only [CollatzResearch.WordTrace]
  refine ⟨81129438951491119573795837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108172585268654826098394449 81129438951491119573795837)
  ·
    refine ⟨30423539606809169840173439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81129438951491119573795837 30423539606809169840173439)
    ·
      refine ⟨45635309410213754760260159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30423539606809169840173439 45635309410213754760260159)
      ·
        refine ⟨68452964115320632140390239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45635309410213754760260159 68452964115320632140390239)
        ·
          refine ⟨102679446172980948210585359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68452964115320632140390239 102679446172980948210585359)
          ·
            refine ⟨154019169259471422315878039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102679446172980948210585359 154019169259471422315878039)
            ·
              refine ⟨231028753889207133473817059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154019169259471422315878039 231028753889207133473817059)
              ·
                refine ⟨346543130833810700210725589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231028753889207133473817059 346543130833810700210725589)
                ·
                  refine ⟨8122104628917438286188881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 346543130833810700210725589 8122104628917438286188881)
                  ·
                    refine ⟨6091578471688078714641661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8122104628917438286188881 6091578471688078714641661)
                    ·
                      refine ⟨2284341926883029517990623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091578471688078714641661 2284341926883029517990623)
                      ·
                        rfl

theorem cell23_4448740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_4448740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448740 prefixEnd_4448740 := by exact prefixLift 4448740
  have htrace : WordTrace (prefixWord ++ tailWord_4448740) baseStart_4448740 baseEnd_4448740 := by
    simpa [prefixWord, tailWord_4448740, baseEnd_4448740] using wordTrace_append hprefix tailTrace_4448740
  have hstable : (prefixWord ++ tailWord_4448740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448740).length < 2 ^ (prefixWord ++ tailWord_4448740).sum := by decide
  have hdescent : baseEnd_4448740 < baseStart_4448740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448750 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4448750 : Nat := 118140960795 + 4448750 * 2 ^ 59
def prefixEnd_4448750 : Nat := 4983230072969 + 3 ^ 40 * 4448750 * 2
def baseEnd_4448750 : Nat := 2284347061689574478865577

theorem tailTrace_4448750 : CollatzResearch.WordTrace tailWord_4448750 prefixEnd_4448750 2284347061689574478865577 := by
  unfold tailWord_4448750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20282405329118251356931963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108172828421964007236970469 20282405329118251356931963)
  ·
    refine ⟨30423607993677377035397945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20282405329118251356931963 30423607993677377035397945)
    ·
      refine ⟨22817705995258032776548459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30423607993677377035397945 22817705995258032776548459)
      ·
        refine ⟨34226558992887049164822689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22817705995258032776548459 34226558992887049164822689)
        ·
          refine ⟨25669919244665286873617017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34226558992887049164822689 25669919244665286873617017)
          ·
            refine ⟨19252439433498965155212763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25669919244665286873617017 19252439433498965155212763)
            ·
              refine ⟨28878659150248447732819145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19252439433498965155212763 28878659150248447732819145)
              ·
                refine ⟨21658994362686335799614359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28878659150248447732819145 21658994362686335799614359)
                ·
                  refine ⟨32488491544029503699421539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21658994362686335799614359 32488491544029503699421539)
                  ·
                    refine ⟨48732737316044255549132309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32488491544029503699421539 48732737316044255549132309)
                    ·
                      refine ⟨2284347061689574478865577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48732737316044255549132309 2284347061689574478865577)
                      ·
                        rfl

theorem cell23_4448750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4448750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448750 prefixEnd_4448750 := by exact prefixLift 4448750
  have htrace : WordTrace (prefixWord ++ tailWord_4448750) baseStart_4448750 baseEnd_4448750 := by
    simpa [prefixWord, tailWord_4448750, baseEnd_4448750] using wordTrace_append hprefix tailTrace_4448750
  have hstable : (prefixWord ++ tailWord_4448750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448750).length < 2 ^ (prefixWord ++ tailWord_4448750).sum := by decide
  have hdescent : baseEnd_4448750 < baseStart_4448750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448791 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4448791 : Nat := 118140960795 + 4448791 * 2 ^ 59
def prefixEnd_4448791 : Nat := 4983230072969 + 3 ^ 40 * 4448791 * 2
def baseEnd_4448791 : Nat := 2284368114396408818452889

theorem tailTrace_4448791 : CollatzResearch.WordTrace tailWord_4448791 prefixEnd_4448791 2284368114396408818452889 := by
  unfold tailWord_4448791
  simp only [CollatzResearch.WordTrace]
  refine ⟨162260738025797474857698227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108173825350531649905132151 162260738025797474857698227)
  ·
    refine ⟨243391107038696212286547341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162260738025797474857698227 243391107038696212286547341)
    ·
      refine ⟨91271665139511079607455253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243391107038696212286547341 91271665139511079607455253)
      ·
        refine ⟨4278359303414581856599465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91271665139511079607455253 4278359303414581856599465)
        ·
          refine ⟨3208769477560936392449599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278359303414581856599465 3208769477560936392449599)
          ·
            refine ⟨4813154216341404588674399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208769477560936392449599 4813154216341404588674399)
            ·
              refine ⟨7219731324512106883011599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813154216341404588674399 7219731324512106883011599)
              ·
                refine ⟨10829596986768160324517399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7219731324512106883011599 10829596986768160324517399)
                ·
                  refine ⟨16244395480152240486776099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10829596986768160324517399 16244395480152240486776099)
                  ·
                    refine ⟨24366593220228360730164149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16244395480152240486776099 24366593220228360730164149)
                    ·
                      refine ⟨2284368114396408818452889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24366593220228360730164149 2284368114396408818452889)
                      ·
                        rfl

theorem cell23_4448791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4448791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448791 prefixEnd_4448791 := by exact prefixLift 4448791
  have htrace : WordTrace (prefixWord ++ tailWord_4448791) baseStart_4448791 baseEnd_4448791 := by
    simpa [prefixWord, tailWord_4448791, baseEnd_4448791] using wordTrace_append hprefix tailTrace_4448791
  have hstable : (prefixWord ++ tailWord_4448791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448791).length < 2 ^ (prefixWord ++ tailWord_4448791).sum := by decide
  have hdescent : baseEnd_4448791 < baseStart_4448791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448793 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_4448793 : Nat := 118140960795 + 4448793 * 2 ^ 59
def prefixEnd_4448793 : Nat := 4983230072969 + 3 ^ 40 * 4448793 * 2
def baseEnd_4448793 : Nat := 2284369141357717810627879

theorem tailTrace_4448793 : CollatzResearch.WordTrace tailWord_4448793 prefixEnd_4448793 2284369141357717810627879 := by
  unfold tailWord_4448793
  simp only [CollatzResearch.WordTrace]
  refine ⟨162260810971790229199271033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108173873981193486132847355 162260810971790229199271033)
  ·
    refine ⟨121695608228842671899453275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162260810971790229199271033 121695608228842671899453275)
    ·
      refine ⟨182543412343264007849179913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121695608228842671899453275 182543412343264007849179913)
      ·
        refine ⟨136907559257448005886884935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182543412343264007849179913 136907559257448005886884935)
        ·
          refine ⟨205361338886172008830327403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136907559257448005886884935 205361338886172008830327403)
          ·
            refine ⟨308042008329258013245491105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205361338886172008830327403 308042008329258013245491105)
            ·
              refine ⟨231031506246943509934118329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308042008329258013245491105 231031506246943509934118329)
              ·
                refine ⟨173273629685207632450588747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231031506246943509934118329 173273629685207632450588747)
                ·
                  refine ⟨259910444527811448675883121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173273629685207632450588747 259910444527811448675883121)
                  ·
                    refine ⟨194932833395858586506912341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259910444527811448675883121 194932833395858586506912341)
                    ·
                      refine ⟨2284369141357717810627879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194932833395858586506912341 2284369141357717810627879)
                      ·
                        rfl

theorem cell23_4448793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_4448793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448793 prefixEnd_4448793 := by exact prefixLift 4448793
  have htrace : WordTrace (prefixWord ++ tailWord_4448793) baseStart_4448793 baseEnd_4448793 := by
    simpa [prefixWord, tailWord_4448793, baseEnd_4448793] using wordTrace_append hprefix tailTrace_4448793
  have hstable : (prefixWord ++ tailWord_4448793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448793).length < 2 ^ (prefixWord ++ tailWord_4448793).sum := by decide
  have hdescent : baseEnd_4448793 < baseStart_4448793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448844 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4448844 : Nat := 118140960795 + 4448844 * 2 ^ 59
def prefixEnd_4448844 : Nat := 4983230072969 + 3 ^ 40 * 4448844 * 2
def baseEnd_4448844 : Nat := 2284395328871097111090145

theorem tailTrace_4448844 : CollatzResearch.WordTrace tailWord_4448844 prefixEnd_4448844 2284395328871097111090145 := by
  unfold tailWord_4448844
  simp only [CollatzResearch.WordTrace]
  refine ⟨81131335547302732454688793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108175114063070309939585057 81131335547302732454688793)
  ·
    refine ⟨60848501660477049341016595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81131335547302732454688793 60848501660477049341016595)
    ·
      refine ⟨91272752490715574011524893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60848501660477049341016595 91272752490715574011524893)
      ·
        refine ⟨34227282184018340254321835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91272752490715574011524893 34227282184018340254321835)
        ·
          refine ⟨51340923276027510381482753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34227282184018340254321835 51340923276027510381482753)
          ·
            refine ⟨38505692457020632786112065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51340923276027510381482753 38505692457020632786112065)
            ·
              refine ⟨28879269342765474589584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38505692457020632786112065 28879269342765474589584049)
              ·
                refine ⟨21659452007074105942188037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28879269342765474589584049 21659452007074105942188037)
                ·
                  refine ⟨4061147251326394864160257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21659452007074105942188037 4061147251326394864160257)
                  ·
                    refine ⟨3045860438494796148120193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061147251326394864160257 3045860438494796148120193)
                    ·
                      refine ⟨2284395328871097111090145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045860438494796148120193 2284395328871097111090145)
                      ·
                        rfl

theorem cell23_4448844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4448844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448844 prefixEnd_4448844 := by exact prefixLift 4448844
  have htrace : WordTrace (prefixWord ++ tailWord_4448844) baseStart_4448844 baseEnd_4448844 := by
    simpa [prefixWord, tailWord_4448844, baseEnd_4448844] using wordTrace_append hprefix tailTrace_4448844
  have hstable : (prefixWord ++ tailWord_4448844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448844).length < 2 ^ (prefixWord ++ tailWord_4448844).sum := by decide
  have hdescent : baseEnd_4448844 < baseStart_4448844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448850 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_4448850 : Nat := 118140960795 + 4448850 * 2 ^ 59
def prefixEnd_4448850 : Nat := 4983230072969 + 3 ^ 40 * 4448850 * 2
def baseEnd_4448850 : Nat := 253822045528336009735013

theorem tailTrace_4448850 : CollatzResearch.WordTrace tailWord_4448850 prefixEnd_4448850 253822045528336009735013 := by
  unfold tailWord_4448850
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565722483145931983524001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108175259955055818622730669 40565722483145931983524001)
  ·
    refine ⟨30424291862359448987643001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40565722483145931983524001 30424291862359448987643001)
    ·
      refine ⟨22818218896769586740732251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30424291862359448987643001 22818218896769586740732251)
      ·
        refine ⟨34227328345154380111098377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22818218896769586740732251 34227328345154380111098377)
        ·
          refine ⟨25670496258865785083323783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34227328345154380111098377 25670496258865785083323783)
          ·
            refine ⟨38505744388298677624985675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25670496258865785083323783 38505744388298677624985675)
            ·
              refine ⟨57758616582448016437478513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38505744388298677624985675 57758616582448016437478513)
              ·
                refine ⟨43318962436836012328108885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57758616582448016437478513 43318962436836012328108885)
                ·
                  refine ⟨253822045528336009735013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43318962436836012328108885 253822045528336009735013)
                  ·
                    rfl

theorem cell23_4448850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_4448850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448850 prefixEnd_4448850 := by exact prefixLift 4448850
  have htrace : WordTrace (prefixWord ++ tailWord_4448850) baseStart_4448850 baseEnd_4448850 := by
    simpa [prefixWord, tailWord_4448850, baseEnd_4448850] using wordTrace_append hprefix tailTrace_4448850
  have hstable : (prefixWord ++ tailWord_4448850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448850).length < 2 ^ (prefixWord ++ tailWord_4448850).sum := by decide
  have hdescent : baseEnd_4448850 < baseStart_4448850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448867 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 5]
def baseStart_4448867 : Nat := 118140960795 + 4448867 * 2 ^ 59
def prefixEnd_4448867 : Nat := 4983230072969 + 3 ^ 40 * 4448867 * 2
def baseEnd_4448867 : Nat := 253823015436238946789171

theorem tailTrace_4448867 : CollatzResearch.WordTrace tailWord_4448867 prefixEnd_4448867 253823015436238946789171 := by
  unfold tailWord_4448867
  simp only [CollatzResearch.WordTrace]
  refine ⟨162263509973522139837464855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108175673315681426558309903 162263509973522139837464855)
  ·
    refine ⟨243395264960283209756197283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162263509973522139837464855 243395264960283209756197283)
    ·
      refine ⟨365092897440424814634295925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243395264960283209756197283 365092897440424814634295925)
      ·
        refine ⟨34227459135039826371965243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 365092897440424814634295925 34227459135039826371965243)
        ·
          refine ⟨51341188702559739557947865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34227459135039826371965243 51341188702559739557947865)
          ·
            refine ⟨38505891526919804668460899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51341188702559739557947865 38505891526919804668460899)
            ·
              refine ⟨57758837290379707002691349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38505891526919804668460899 57758837290379707002691349)
              ·
                refine ⟨2707445497986548765751157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57758837290379707002691349 2707445497986548765751157)
                ·
                  refine ⟨253823015436238946789171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2707445497986548765751157 253823015436238946789171)
                  ·
                    rfl

theorem cell23_4448867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 5].length) (baseStart_4448867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448867 prefixEnd_4448867 := by exact prefixLift 4448867
  have htrace : WordTrace (prefixWord ++ tailWord_4448867) baseStart_4448867 baseEnd_4448867 := by
    simpa [prefixWord, tailWord_4448867, baseEnd_4448867] using wordTrace_append hprefix tailTrace_4448867
  have hstable : (prefixWord ++ tailWord_4448867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448867).length < 2 ^ (prefixWord ++ tailWord_4448867).sum := by decide
  have hdescent : baseEnd_4448867 < baseStart_4448867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448887 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_4448887 : Nat := 118140960795 + 4448887 * 2 ^ 59
def prefixEnd_4448887 : Nat := 4983230072969 + 3 ^ 40 * 4448887 * 2
def baseEnd_4448887 : Nat := 2284417408539240442852447

theorem tailTrace_4448887 : CollatzResearch.WordTrace tailWord_4448887 prefixEnd_4448887 2284417408539240442852447 := by
  unfold tailWord_4448887
  simp only [CollatzResearch.WordTrace]
  refine ⟨162264239433449683253192915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108176159622299788835461943 162264239433449683253192915)
  ·
    refine ⟨243396359150174524879789373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162264239433449683253192915 243396359150174524879789373)
    ·
      refine ⟨91273634681315446829921015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243396359150174524879789373 91273634681315446829921015)
      ·
        refine ⟨136910452021973170244881523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91273634681315446829921015 136910452021973170244881523)
        ·
          refine ⟨205365678032959755367322285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136910452021973170244881523 205365678032959755367322285)
          ·
            refine ⟨77012129262359908262745857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205365678032959755367322285 77012129262359908262745857)
            ·
              refine ⟨57759096946769931197059393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77012129262359908262745857 57759096946769931197059393)
              ·
                refine ⟨43319322710077448397794545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57759096946769931197059393 43319322710077448397794545)
                ·
                  refine ⟨32489492032558086298345909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43319322710077448397794545 32489492032558086298345909)
                  ·
                    refine ⟨3045889878052320590469929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32489492032558086298345909 3045889878052320590469929)
                    ·
                      refine ⟨2284417408539240442852447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045889878052320590469929 2284417408539240442852447)
                      ·
                        rfl

theorem cell23_4448887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_4448887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448887 prefixEnd_4448887 := by exact prefixLift 4448887
  have htrace : WordTrace (prefixWord ++ tailWord_4448887) baseStart_4448887 baseEnd_4448887 := by
    simpa [prefixWord, tailWord_4448887, baseEnd_4448887] using wordTrace_append hprefix tailTrace_4448887
  have hstable : (prefixWord ++ tailWord_4448887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448887).length < 2 ^ (prefixWord ++ tailWord_4448887).sum := by decide
  have hdescent : baseEnd_4448887 < baseStart_4448887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448897 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4448897 : Nat := 118140960795 + 4448897 * 2 ^ 59
def prefixEnd_4448897 : Nat := 4983230072969 + 3 ^ 40 * 4448897 * 2
def baseEnd_4448897 : Nat := 761474181115261801242467

theorem tailTrace_4448897 : CollatzResearch.WordTrace tailWord_4448897 prefixEnd_4448897 761474181115261801242467 := by
  unfold tailWord_4448897
  simp only [CollatzResearch.WordTrace]
  refine ⟨162264604163413454961056945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108176402775608969974037963 162264604163413454961056945)
  ·
    refine ⟨121698453122560091220792709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162264604163413454961056945 121698453122560091220792709)
    ·
      refine ⟨22818459960480017103898633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121698453122560091220792709 22818459960480017103898633)
      ·
        refine ⟨17113844970360012827923975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22818459960480017103898633 17113844970360012827923975)
        ·
          refine ⟨25670767455540019241885963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17113844970360012827923975 25670767455540019241885963)
          ·
            refine ⟨38506151183310028862828945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25670767455540019241885963 38506151183310028862828945)
            ·
              refine ⟨28879613387482521647121709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38506151183310028862828945 28879613387482521647121709)
              ·
                refine ⟨10829855020305945617670641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28879613387482521647121709 10829855020305945617670641)
                ·
                  refine ⟨8122391265229459213252981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10829855020305945617670641 8122391265229459213252981)
                  ·
                    refine ⟨761474181115261801242467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8122391265229459213252981 761474181115261801242467)
                    ·
                      rfl

theorem cell23_4448897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4448897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448897 prefixEnd_4448897 := by exact prefixLift 4448897
  have htrace : WordTrace (prefixWord ++ tailWord_4448897) baseStart_4448897 baseEnd_4448897 := by
    simpa [prefixWord, tailWord_4448897, baseEnd_4448897] using wordTrace_append hprefix tailTrace_4448897
  have hstable : (prefixWord ++ tailWord_4448897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448897).length < 2 ^ (prefixWord ++ tailWord_4448897).sum := by decide
  have hdescent : baseEnd_4448897 < baseStart_4448897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448898 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4448898 : Nat := 118140960795 + 4448898 * 2 ^ 59
def prefixEnd_4448898 : Nat := 4983230072969 + 3 ^ 40 * 4448898 * 2
def baseEnd_4448898 : Nat := 2284423056826439899814897

theorem tailTrace_4448898 : CollatzResearch.WordTrace tailWord_4448898 prefixEnd_4448898 2284423056826439899814897 := by
  unfold tailWord_4448898
  simp only [CollatzResearch.WordTrace]
  refine ⟨40566160159102458032960837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108176427090939888087895565 40566160159102458032960837)
  ·
    refine ⟨7606155029831710881180157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40566160159102458032960837 7606155029831710881180157)
    ·
      refine ⟨2852308136186891580442559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7606155029831710881180157 2852308136186891580442559)
      ·
        refine ⟨4278462204280337370663839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852308136186891580442559 4278462204280337370663839)
        ·
          refine ⟨6417693306420506055995759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278462204280337370663839 6417693306420506055995759)
          ·
            refine ⟨9626539959630759083993639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417693306420506055995759 9626539959630759083993639)
            ·
              refine ⟨14439809939446138625990459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626539959630759083993639 14439809939446138625990459)
              ·
                refine ⟨21659714909169207938985689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14439809939446138625990459 21659714909169207938985689)
                ·
                  refine ⟨16244786181876905954239267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21659714909169207938985689 16244786181876905954239267)
                  ·
                    refine ⟨24367179272815358931358901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16244786181876905954239267 24367179272815358931358901)
                    ·
                      refine ⟨2284423056826439899814897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24367179272815358931358901 2284423056826439899814897)
                      ·
                        rfl

theorem cell23_4448898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4448898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448898 prefixEnd_4448898 := by exact prefixLift 4448898
  have htrace : WordTrace (prefixWord ++ tailWord_4448898) baseStart_4448898 baseEnd_4448898 := by
    simpa [prefixWord, tailWord_4448898, baseEnd_4448898] using wordTrace_append hprefix tailTrace_4448898
  have hstable : (prefixWord ++ tailWord_4448898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448898).length < 2 ^ (prefixWord ++ tailWord_4448898).sum := by decide
  have hdescent : baseEnd_4448898 < baseStart_4448898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448914 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4448914 : Nat := 118140960795 + 4448914 * 2 ^ 59
def prefixEnd_4448914 : Nat := 4983230072969 + 3 ^ 40 * 4448914 * 2
def baseEnd_4448914 : Nat := 761477090838970612404941

theorem tailTrace_4448914 : CollatzResearch.WordTrace tailWord_4448914 prefixEnd_4448914 761477090838970612404941 := by
  unfold tailWord_4448914
  simp only [CollatzResearch.WordTrace]
  refine ⟨40566306051087966716106449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108176816136234577909617197 40566306051087966716106449)
  ·
    refine ⟨30424729538315975037079837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40566306051087966716106449 30424729538315975037079837)
    ·
      refine ⟨11409273576868490638904939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30424729538315975037079837 11409273576868490638904939)
      ·
        refine ⟨17113910365302735958357409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11409273576868490638904939 17113910365302735958357409)
        ·
          refine ⟨12835432773977051968768057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17113910365302735958357409 12835432773977051968768057)
          ·
            refine ⟨9626574580482788976576043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12835432773977051968768057 9626574580482788976576043)
            ·
              refine ⟨14439861870724183464864065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626574580482788976576043 14439861870724183464864065)
              ·
                refine ⟨10829896403043137598648049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14439861870724183464864065 10829896403043137598648049)
                ·
                  refine ⟨8122422302282353198986037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10829896403043137598648049 8122422302282353198986037)
                  ·
                    refine ⟨761477090838970612404941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8122422302282353198986037 761477090838970612404941)
                    ·
                      rfl

theorem cell23_4448914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4448914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448914 prefixEnd_4448914 := by exact prefixLift 4448914
  have htrace : WordTrace (prefixWord ++ tailWord_4448914) baseStart_4448914 baseEnd_4448914 := by
    simpa [prefixWord, tailWord_4448914, baseEnd_4448914] using wordTrace_append hprefix tailTrace_4448914
  have hstable : (prefixWord ++ tailWord_4448914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448914).length < 2 ^ (prefixWord ++ tailWord_4448914).sum := by decide
  have hdescent : baseEnd_4448914 < baseStart_4448914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448954 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_4448954 : Nat := 118140960795 + 4448954 * 2 ^ 59
def prefixEnd_4448954 : Nat := 4983230072969 + 3 ^ 40 * 4448954 * 2
def baseEnd_4448954 : Nat := 2284451811743091680714639

theorem tailTrace_4448954 : CollatzResearch.WordTrace tailWord_4448954 prefixEnd_4448954 2284451811743091680714639 := by
  unfold tailWord_4448954
  simp only [CollatzResearch.WordTrace]
  refine ⟨40566670781051738423970479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108177788749471302463921277 40566670781051738423970479)
  ·
    refine ⟨60850006171577607635955719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40566670781051738423970479 60850006171577607635955719)
    ·
      refine ⟨91275009257366411453933579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60850006171577607635955719 91275009257366411453933579)
      ·
        refine ⟨136912513886049617180900369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91275009257366411453933579 136912513886049617180900369)
        ·
          refine ⟨102684385414537212885675277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136912513886049617180900369 102684385414537212885675277)
          ·
            refine ⟨38506644530451454832128229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102684385414537212885675277 38506644530451454832128229)
            ·
              refine ⟨7219995849459647781024043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38506644530451454832128229 7219995849459647781024043)
              ·
                refine ⟨10829993774189471671536065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7219995849459647781024043 10829993774189471671536065)
                ·
                  refine ⟨8122495330642103753652049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10829993774189471671536065 8122495330642103753652049)
                  ·
                    refine ⟨6091871497981577815239037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8122495330642103753652049 6091871497981577815239037)
                    ·
                      refine ⟨2284451811743091680714639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6091871497981577815239037 2284451811743091680714639)
                      ·
                        rfl

theorem cell23_4448954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_4448954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448954 prefixEnd_4448954 := by exact prefixLift 4448954
  have htrace : WordTrace (prefixWord ++ tailWord_4448954) baseStart_4448954 baseEnd_4448954 := by
    simpa [prefixWord, tailWord_4448954, baseEnd_4448954] using wordTrace_append hprefix tailTrace_4448954
  have hstable : (prefixWord ++ tailWord_4448954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448954).length < 2 ^ (prefixWord ++ tailWord_4448954).sum := by decide
  have hdescent : baseEnd_4448954 < baseStart_4448954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448974 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_4448974 : Nat := 118140960795 + 4448974 * 2 ^ 59
def prefixEnd_4448974 : Nat := 4983230072969 + 3 ^ 40 * 4448974 * 2
def baseEnd_4448974 : Nat := 253829120150686844718283

theorem tailTrace_4448974 : CollatzResearch.WordTrace tailWord_4448974 prefixEnd_4448974 253829120150686844718283 := by
  unfold tailWord_4448974
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283426573016812138951247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108178275056089664741073317 20283426573016812138951247)
  ·
    refine ⟨30425139859525218208426871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20283426573016812138951247 30425139859525218208426871)
    ·
      refine ⟨45637709789287827312640307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30425139859525218208426871 45637709789287827312640307)
      ·
        refine ⟨68456564683931740968960461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45637709789287827312640307 68456564683931740968960461)
        ·
          refine ⟨25671211756474402863360173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68456564683931740968960461 25671211756474402863360173)
          ·
            refine ⟨9626704408677901073760065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25671211756474402863360173 9626704408677901073760065)
            ·
              refine ⟨7220028306508425805320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9626704408677901073760065 7220028306508425805320049)
              ·
                refine ⟨5415021229881319353990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7220028306508425805320049 5415021229881319353990037)
                ·
                  refine ⟨253829120150686844718283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5415021229881319353990037 253829120150686844718283)
                  ·
                    rfl

theorem cell23_4448974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_4448974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448974 prefixEnd_4448974 := by exact prefixLift 4448974
  have htrace : WordTrace (prefixWord ++ tailWord_4448974) baseStart_4448974 baseEnd_4448974 := by
    simpa [prefixWord, tailWord_4448974, baseEnd_4448974] using wordTrace_append hprefix tailTrace_4448974
  have hstable : (prefixWord ++ tailWord_4448974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448974).length < 2 ^ (prefixWord ++ tailWord_4448974).sum := by decide
  have hdescent : baseEnd_4448974 < baseStart_4448974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4448978 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_4448978 : Nat := 118140960795 + 4448978 * 2 ^ 59
def prefixEnd_4448978 : Nat := 4983230072969 + 3 ^ 40 * 4448978 * 2
def baseEnd_4448978 : Nat := 761488045092933195604843

theorem tailTrace_4448978 : CollatzResearch.WordTrace tailWord_4448978 prefixEnd_4448978 761488045092933195604843 := by
  unfold tailWord_4448978
  simp only [CollatzResearch.WordTrace]
  refine ⟨40566889619030001448688897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108178372317413337196503725 40566889619030001448688897)
  ·
    refine ⟨30425167214272501086516673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40566889619030001448688897 30425167214272501086516673)
    ·
      refine ⟨22818875410704375814887505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30425167214272501086516673 22818875410704375814887505)
      ·
        refine ⟨17114156558028281861165629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22818875410704375814887505 17114156558028281861165629)
        ·
          refine ⟨6417808709260605697937111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17114156558028281861165629 6417808709260605697937111)
          ·
            refine ⟨9626713063890908546905667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417808709260605697937111 9626713063890908546905667)
            ·
              refine ⟨14440069595836362820358501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626713063890908546905667 14440069595836362820358501)
              ·
                refine ⟨2707513049219318028817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14440069595836362820358501 2707513049219318028817219)
                ·
                  refine ⟨4061269573828977043225829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707513049219318028817219 4061269573828977043225829)
                  ·
                    refine ⟨761488045092933195604843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061269573828977043225829 761488045092933195604843)
                    ·
                      rfl

theorem cell23_4448978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_4448978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4448978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4448978 prefixEnd_4448978 := by exact prefixLift 4448978
  have htrace : WordTrace (prefixWord ++ tailWord_4448978) baseStart_4448978 baseEnd_4448978 := by
    simpa [prefixWord, tailWord_4448978, baseEnd_4448978] using wordTrace_append hprefix tailTrace_4448978
  have hstable : (prefixWord ++ tailWord_4448978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4448978).length < 2 ^ (prefixWord ++ tailWord_4448978).sum := by decide
  have hdescent : baseEnd_4448978 < baseStart_4448978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4448978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449012 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4449012 : Nat := 118140960795 + 4449012 * 2 ^ 59
def prefixEnd_4449012 : Nat := 4983230072969 + 3 ^ 40 * 4449012 * 2
def baseEnd_4449012 : Nat := 761493864540350817929791

theorem tailTrace_4449012 : CollatzResearch.WordTrace tailWord_4449012 prefixEnd_4449012 761493864540350817929791 := by
  unfold tailWord_4449012
  simp only [CollatzResearch.WordTrace]
  refine ⟨81134399278998414800746645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108179199038664553067662193 81134399278998414800746645)
  ·
    refine ⟨3803174966203050693784999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81134399278998414800746645 3803174966203050693784999)
    ·
      refine ⟨5704762449304576040677499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803174966203050693784999 5704762449304576040677499)
      ·
        refine ⟨8557143673956864061016249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704762449304576040677499 8557143673956864061016249)
        ·
          refine ⟨6417857755467648045762187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8557143673956864061016249 6417857755467648045762187)
          ·
            refine ⟨9626786633201472068643281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417857755467648045762187 9626786633201472068643281)
            ·
              refine ⟨7220089974901104051482461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9626786633201472068643281 7220089974901104051482461)
              ·
                refine ⟨2707533740587914019305923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7220089974901104051482461 2707533740587914019305923)
                ·
                  refine ⟨4061300610881871028958885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707533740587914019305923 4061300610881871028958885)
                  ·
                    refine ⟨761493864540350817929791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061300610881871028958885 761493864540350817929791)
                    ·
                      rfl

theorem cell23_4449012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4449012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449012 prefixEnd_4449012 := by exact prefixLift 4449012
  have htrace : WordTrace (prefixWord ++ tailWord_4449012) baseStart_4449012 baseEnd_4449012 := by
    simpa [prefixWord, tailWord_4449012, baseEnd_4449012] using wordTrace_append hprefix tailTrace_4449012
  have hstable : (prefixWord ++ tailWord_4449012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449012).length < 2 ^ (prefixWord ++ tailWord_4449012).sum := by decide
  have hdescent : baseEnd_4449012 < baseStart_4449012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_4449027 : Nat := 118140960795 + 4449027 * 2 ^ 59
def prefixEnd_4449027 : Nat := 4983230072969 + 3 ^ 40 * 4449027 * 2
def baseEnd_4449027 : Nat := 2284489295830869895101803

theorem tailTrace_4449027 : CollatzResearch.WordTrace tailWord_4449027 prefixEnd_4449027 2284489295830869895101803 := by
  unfold tailWord_4449027
  simp only [CollatzResearch.WordTrace]
  refine ⟨162269345652942487163289335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108179563768628324775526223 162269345652942487163289335)
  ·
    refine ⟨243404018479413730744934003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162269345652942487163289335 243404018479413730744934003)
    ·
      refine ⟨365106027719120596117401005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243404018479413730744934003 365106027719120596117401005)
      ·
        refine ⟨136914760394670223544025377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365106027719120596117401005 136914760394670223544025377)
        ·
          refine ⟨102686070296002667658019033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136914760394670223544025377 102686070296002667658019033)
          ·
            refine ⟨77014552722002000743514275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102686070296002667658019033 77014552722002000743514275)
            ·
              refine ⟨115521829083003001115271413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77014552722002000743514275 115521829083003001115271413)
              ·
                refine ⟨10830171476531531354556695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115521829083003001115271413 10830171476531531354556695)
                ·
                  refine ⟨16245257214797297031835043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10830171476531531354556695 16245257214797297031835043)
                  ·
                    refine ⟨24367885822195945547752565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16245257214797297031835043 24367885822195945547752565)
                    ·
                      refine ⟨2284489295830869895101803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24367885822195945547752565 2284489295830869895101803)
                      ·
                        rfl

theorem cell23_4449027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_4449027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449027 prefixEnd_4449027 := by exact prefixLift 4449027
  have htrace : WordTrace (prefixWord ++ tailWord_4449027) baseStart_4449027 baseEnd_4449027 := by
    simpa [prefixWord, tailWord_4449027, baseEnd_4449027] using wordTrace_append hprefix tailTrace_4449027
  have hstable : (prefixWord ++ tailWord_4449027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449027).length < 2 ^ (prefixWord ++ tailWord_4449027).sum := by decide
  have hdescent : baseEnd_4449027 < baseStart_4449027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449034 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_4449034 : Nat := 118140960795 + 4449034 * 2 ^ 59
def prefixEnd_4449034 : Nat := 4983230072969 + 3 ^ 40 * 4449034 * 2
def baseEnd_4449034 : Nat := 761497630065150455904757

theorem tailTrace_4449034 : CollatzResearch.WordTrace tailWord_4449034 prefixEnd_4449034 761497630065150455904757 := by
  unfold tailWord_4449034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567400240979281839698539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108179733975944751572529437 40567400240979281839698539)
  ·
    refine ⟨60851100361468922759547809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40567400240979281839698539 60851100361468922759547809)
    ·
      refine ⟨45638325271101692069660857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60851100361468922759547809 45638325271101692069660857)
      ·
        refine ⟨34228743953326269052245643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45638325271101692069660857 34228743953326269052245643)
        ·
          refine ⟨51343115929989403578368465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34228743953326269052245643 51343115929989403578368465)
          ·
            refine ⟨38507336947492052683776349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51343115929989403578368465 38507336947492052683776349)
            ·
              refine ⟨14440251355309519756416131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38507336947492052683776349 14440251355309519756416131)
              ·
                refine ⟨21660377032964279634624197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14440251355309519756416131 21660377032964279634624197)
                ·
                  refine ⟨4061320693680802431492037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21660377032964279634624197 4061320693680802431492037)
                  ·
                    refine ⟨761497630065150455904757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061320693680802431492037 761497630065150455904757)
                    ·
                      rfl

theorem cell23_4449034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_4449034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449034 prefixEnd_4449034 := by exact prefixLift 4449034
  have htrace : WordTrace (prefixWord ++ tailWord_4449034) baseStart_4449034 baseEnd_4449034 := by
    simpa [prefixWord, tailWord_4449034, baseEnd_4449034] using wordTrace_append hprefix tailTrace_4449034
  have hstable : (prefixWord ++ tailWord_4449034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449034).length < 2 ^ (prefixWord ++ tailWord_4449034).sum := by decide
  have hdescent : baseEnd_4449034 < baseStart_4449034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449041 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_4449041 : Nat := 118140960795 + 4449041 * 2 ^ 59
def prefixEnd_4449041 : Nat := 4983230072969 + 3 ^ 40 * 4449041 * 2
def baseEnd_4449041 : Nat := 2284496484560032840326739

theorem tailTrace_4449041 : CollatzResearch.WordTrace tailWord_4449041 prefixEnd_4449041 2284496484560032840326739 := by
  unfold tailWord_4449041
  simp only [CollatzResearch.WordTrace]
  refine ⟨162269856274891767554298977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108179904183261178369532651 162269856274891767554298977)
  ·
    refine ⟨121702392206168825665724233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162269856274891767554298977 121702392206168825665724233)
    ·
      refine ⟨91276794154626619249293175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121702392206168825665724233 91276794154626619249293175)
      ·
        refine ⟨136915191231939928873939763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91276794154626619249293175 136915191231939928873939763)
        ·
          refine ⟨205372786847909893310909645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136915191231939928873939763 205372786847909893310909645)
          ·
            refine ⟨77014795067966209991591117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205372786847909893310909645 77014795067966209991591117)
            ·
              refine ⟨28880548150487328746846669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77014795067966209991591117 28880548150487328746846669)
              ·
                refine ⟨10830205556432748280067501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28880548150487328746846669 10830205556432748280067501)
                ·
                  refine ⟨4061327083662280605025313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10830205556432748280067501 4061327083662280605025313)
                  ·
                    refine ⟨3045995312746710453768985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061327083662280605025313 3045995312746710453768985)
                    ·
                      refine ⟨2284496484560032840326739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3045995312746710453768985 2284496484560032840326739)
                      ·
                        rfl

theorem cell23_4449041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_4449041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449041 prefixEnd_4449041 := by exact prefixLift 4449041
  have htrace : WordTrace (prefixWord ++ tailWord_4449041) baseStart_4449041 baseEnd_4449041 := by
    simpa [prefixWord, tailWord_4449041, baseEnd_4449041] using wordTrace_append hprefix tailTrace_4449041
  have hstable : (prefixWord ++ tailWord_4449041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449041).length < 2 ^ (prefixWord ++ tailWord_4449041).sum := by decide
  have hdescent : baseEnd_4449041 < baseStart_4449041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449058 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_4449058 : Nat := 118140960795 + 4449058 * 2 ^ 59
def prefixEnd_4449058 : Nat := 4983230072969 + 3 ^ 40 * 4449058 * 2
def baseEnd_4449058 : Nat := 2284505213731159273814161

theorem tailTrace_4449058 : CollatzResearch.WordTrace tailWord_4449058 prefixEnd_4449058 2284505213731159273814161 := by
  unfold tailWord_4449058
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567619078957544864416957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108180317543886786305111885 40567619078957544864416957)
  ·
    refine ⟨15212857154609079324156359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40567619078957544864416957 15212857154609079324156359)
    ·
      refine ⟨22819285731913618986234539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15212857154609079324156359 22819285731913618986234539)
      ·
        refine ⟨34228928597870428479351809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22819285731913618986234539 34228928597870428479351809)
        ·
          refine ⟨25671696448402821359513857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34228928597870428479351809 25671696448402821359513857)
          ·
            refine ⟨19253772336302116019635393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25671696448402821359513857 19253772336302116019635393)
            ·
              refine ⟨14440329252226587014726545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19253772336302116019635393 14440329252226587014726545)
              ·
                refine ⟨10830246939169940261044909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14440329252226587014726545 10830246939169940261044909)
                ·
                  refine ⟨4061342602188727597891841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10830246939169940261044909 4061342602188727597891841)
                  ·
                    refine ⟨3046006951641545698418881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061342602188727597891841 3046006951641545698418881)
                    ·
                      refine ⟨2284505213731159273814161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046006951641545698418881 2284505213731159273814161)
                      ·
                        rfl

theorem cell23_4449058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_4449058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449058 prefixEnd_4449058 := by exact prefixLift 4449058
  have htrace : WordTrace (prefixWord ++ tailWord_4449058) baseStart_4449058 baseEnd_4449058 := by
    simpa [prefixWord, tailWord_4449058, baseEnd_4449058] using wordTrace_append hprefix tailTrace_4449058
  have hstable : (prefixWord ++ tailWord_4449058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449058).length < 2 ^ (prefixWord ++ tailWord_4449058).sum := by decide
  have hdescent : baseEnd_4449058 < baseStart_4449058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449061 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_4449061 : Nat := 118140960795 + 4449061 * 2 ^ 59
def prefixEnd_4449061 : Nat := 4983230072969 + 3 ^ 40 * 4449061 * 2
def baseEnd_4449061 : Nat := 2284506754173122762076647

theorem tailTrace_4449061 : CollatzResearch.WordTrace tailWord_4449061 prefixEnd_4449061 2284506754173122762076647 := by
  unfold tailWord_4449061
  simp only [CollatzResearch.WordTrace]
  refine ⟨162270585734819310970027037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108180390489879540646684691 162270585734819310970027037)
  ·
    refine ⟨60851469650557241613760139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162270585734819310970027037 60851469650557241613760139)
    ·
      refine ⟨91277204475835862420640209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60851469650557241613760139 91277204475835862420640209)
      ·
        refine ⟨68457903356876896815480157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91277204475835862420640209 68457903356876896815480157)
        ·
          refine ⟨25671713758828836305805059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68457903356876896815480157 25671713758828836305805059)
          ·
            refine ⟨38507570638243254458707589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25671713758828836305805059 38507570638243254458707589)
            ·
              refine ⟨7220169494670610211007673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38507570638243254458707589 7220169494670610211007673)
              ·
                refine ⟨5415127121002957658255755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7220169494670610211007673 5415127121002957658255755)
                ·
                  refine ⟨8122690681504436487383633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415127121002957658255755 8122690681504436487383633)
                  ·
                    refine ⟨6092018011128327365537725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8122690681504436487383633 6092018011128327365537725)
                    ·
                      refine ⟨2284506754173122762076647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092018011128327365537725 2284506754173122762076647)
                      ·
                        rfl

theorem cell23_4449061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_4449061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449061 prefixEnd_4449061 := by exact prefixLift 4449061
  have htrace : WordTrace (prefixWord ++ tailWord_4449061) baseStart_4449061 baseEnd_4449061 := by
    simpa [prefixWord, tailWord_4449061, baseEnd_4449061] using wordTrace_append hprefix tailTrace_4449061
  have hstable : (prefixWord ++ tailWord_4449061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449061).length < 2 ^ (prefixWord ++ tailWord_4449061).sum := by decide
  have hdescent : baseEnd_4449061 < baseStart_4449061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449069 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4449069 : Nat := 118140960795 + 4449069 * 2 ^ 59
def prefixEnd_4449069 : Nat := 4983230072969 + 3 ^ 40 * 4449069 * 2
def baseEnd_4449069 : Nat := 2284510862018358730776611

theorem tailTrace_4449069 : CollatzResearch.WordTrace tailWord_4449069 prefixEnd_4449069 2284510862018358730776611 := by
  unfold tailWord_4449069
  simp only [CollatzResearch.WordTrace]
  refine ⟨162270877518790328336318261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108180585012526885557545507 162270877518790328336318261)
  ·
    refine ⟨15212894767386593281529837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162270877518790328336318261 15212894767386593281529837)
    ·
      refine ⟨5704835537769972480573689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15212894767386593281529837 5704835537769972480573689)
      ·
        refine ⟨4278626653327479360430267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5704835537769972480573689 4278626653327479360430267)
        ·
          refine ⟨6417939979991219040645401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278626653327479360430267 6417939979991219040645401)
          ·
            refine ⟨4813454984993414280484051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6417939979991219040645401 4813454984993414280484051)
            ·
              refine ⟨7220182477490121420726077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813454984993414280484051 7220182477490121420726077)
              ·
                refine ⟨2707568429058795532772279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7220182477490121420726077 2707568429058795532772279)
                ·
                  refine ⟨4061352643588193299158419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707568429058795532772279 4061352643588193299158419)
                  ·
                    refine ⟨6092028965382289948737629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061352643588193299158419 6092028965382289948737629)
                    ·
                      refine ⟨2284510862018358730776611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092028965382289948737629 2284510862018358730776611)
                      ·
                        rfl

theorem cell23_4449069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4449069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449069 prefixEnd_4449069 := by exact prefixLift 4449069
  have htrace : WordTrace (prefixWord ++ tailWord_4449069) baseStart_4449069 baseEnd_4449069 := by
    simpa [prefixWord, tailWord_4449069, baseEnd_4449069] using wordTrace_append hprefix tailTrace_4449069
  have hstable : (prefixWord ++ tailWord_4449069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449069).length < 2 ^ (prefixWord ++ tailWord_4449069).sum := by decide
  have hdescent : baseEnd_4449069 < baseStart_4449069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449074 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4449074 : Nat := 118140960795 + 4449074 * 2 ^ 59
def prefixEnd_4449074 : Nat := 4983230072969 + 3 ^ 40 * 4449074 * 2
def baseEnd_4449074 : Nat := 2284513429421631211214087

theorem tailTrace_4449074 : CollatzResearch.WordTrace tailWord_4449074 prefixEnd_4449074 2284513429421631211214087 := by
  unfold tailWord_4449074
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567764970943053547562569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108180706589181476126833517 40567764970943053547562569)
  ·
    refine ⟨30425823728207290160671927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40567764970943053547562569 30425823728207290160671927)
    ·
      refine ⟨45638735592310935241007891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30425823728207290160671927 45638735592310935241007891)
      ·
        refine ⟨68458103388466402861511837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45638735592310935241007891 68458103388466402861511837)
        ·
          refine ⟨25671788770674901073066939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68458103388466402861511837 25671788770674901073066939)
          ·
            refine ⟨38507683156012351609600409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25671788770674901073066939 38507683156012351609600409)
            ·
              refine ⟨28880762367009263707200307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38507683156012351609600409 28880762367009263707200307)
              ·
                refine ⟨43321143550513895560800461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28880762367009263707200307 43321143550513895560800461)
                ·
                  refine ⟨16245428831442710835300173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43321143550513895560800461 16245428831442710835300173)
                  ·
                    refine ⟨6092035811791016563237565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16245428831442710835300173 6092035811791016563237565)
                    ·
                      refine ⟨2284513429421631211214087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092035811791016563237565 2284513429421631211214087)
                      ·
                        rfl

theorem cell23_4449074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4449074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449074 prefixEnd_4449074 := by exact prefixLift 4449074
  have htrace : WordTrace (prefixWord ++ tailWord_4449074) baseStart_4449074 baseEnd_4449074 := by
    simpa [prefixWord, tailWord_4449074, baseEnd_4449074] using wordTrace_append hprefix tailTrace_4449074
  have hstable : (prefixWord ++ tailWord_4449074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449074).length < 2 ^ (prefixWord ++ tailWord_4449074).sum := by decide
  have hdescent : baseEnd_4449074 < baseStart_4449074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449075 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 1, 2, 2]
def baseStart_4449075 : Nat := 118140960795 + 4449075 * 2 ^ 59
def prefixEnd_4449075 : Nat := 4983230072969 + 3 ^ 40 * 4449075 * 2
def baseEnd_4449075 : Nat := 2284513942902285707301583

theorem tailTrace_4449075 : CollatzResearch.WordTrace tailWord_4449075 prefixEnd_4449075 2284513942902285707301583 := by
  unfold tailWord_4449075
  simp only [CollatzResearch.WordTrace]
  refine ⟨162271096356768591361036679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108180730904512394240691119 162271096356768591361036679)
  ·
    refine ⟨243406644535152887041555019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162271096356768591361036679 243406644535152887041555019)
    ·
      refine ⟨365109966802729330562332529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243406644535152887041555019 365109966802729330562332529)
      ·
        refine ⟨273832475102046997921749397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365109966802729330562332529 273832475102046997921749397)
        ·
          refine ⟨12835897270408453027582003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 273832475102046997921749397 12835897270408453027582003)
          ·
            refine ⟨19253845905612679541373005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12835897270408453027582003 19253845905612679541373005)
            ·
              refine ⟨7220192214604754828014877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19253845905612679541373005 7220192214604754828014877)
              ·
                refine ⟨2707572080476783060505579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7220192214604754828014877 2707572080476783060505579)
                ·
                  refine ⟨4061358120715174590758369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707572080476783060505579 4061358120715174590758369)
                  ·
                    refine ⟨3046018590536380943068777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061358120715174590758369 3046018590536380943068777)
                    ·
                      refine ⟨2284513942902285707301583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046018590536380943068777 2284513942902285707301583)
                      ·
                        rfl

theorem cell23_4449075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 2, 2].length) (baseStart_4449075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449075 prefixEnd_4449075 := by exact prefixLift 4449075
  have htrace : WordTrace (prefixWord ++ tailWord_4449075) baseStart_4449075 baseEnd_4449075 := by
    simpa [prefixWord, tailWord_4449075, baseEnd_4449075] using wordTrace_append hprefix tailTrace_4449075
  have hstable : (prefixWord ++ tailWord_4449075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449075).length < 2 ^ (prefixWord ++ tailWord_4449075).sum := by decide
  have hdescent : baseEnd_4449075 < baseStart_4449075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449078 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4449078 : Nat := 118140960795 + 4449078 * 2 ^ 59
def prefixEnd_4449078 : Nat := 4983230072969 + 3 ^ 40 * 4449078 * 2
def baseEnd_4449078 : Nat := 2284515483344249195564069

theorem tailTrace_4449078 : CollatzResearch.WordTrace tailWord_4449078 prefixEnd_4449078 2284515483344249195564069 := by
  unfold tailWord_4449078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141950360984857679587243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108180803850505148582263925 10141950360984857679587243)
  ·
    refine ⟨15212925541477286519380865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10141950360984857679587243 15212925541477286519380865)
    ·
      refine ⟨11409694156107964889535649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15212925541477286519380865 11409694156107964889535649)
      ·
        refine ⟨8557270617080973667151737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11409694156107964889535649 8557270617080973667151737)
        ·
          refine ⟨6417952962810730250363803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8557270617080973667151737 6417952962810730250363803)
          ·
            refine ⟨9626929444216095375545705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417952962810730250363803 9626929444216095375545705)
            ·
              refine ⟨7220197083162071531659279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9626929444216095375545705 7220197083162071531659279)
              ·
                refine ⟨10830295624743107297488919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7220197083162071531659279 10830295624743107297488919)
                ·
                  refine ⟨16245443437114660946233379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10830295624743107297488919 16245443437114660946233379)
                  ·
                    refine ⟨24368165155671991419350069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16245443437114660946233379 24368165155671991419350069)
                    ·
                      refine ⟨2284515483344249195564069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24368165155671991419350069 2284515483344249195564069)
                      ·
                        rfl

theorem cell23_4449078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4449078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449078 prefixEnd_4449078 := by exact prefixLift 4449078
  have htrace : WordTrace (prefixWord ++ tailWord_4449078) baseStart_4449078 baseEnd_4449078 := by
    simpa [prefixWord, tailWord_4449078, baseEnd_4449078] using wordTrace_append hprefix tailTrace_4449078
  have hstable : (prefixWord ++ tailWord_4449078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449078).length < 2 ^ (prefixWord ++ tailWord_4449078).sum := by decide
  have hdescent : baseEnd_4449078 < baseStart_4449078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449091 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 3]
def baseStart_4449091 : Nat := 118140960795 + 4449091 * 2 ^ 59
def prefixEnd_4449091 : Nat := 4983230072969 + 3 ^ 40 * 4449091 * 2
def baseEnd_4449091 : Nat := 2284522158592757644701509

theorem tailTrace_4449091 : CollatzResearch.WordTrace tailWord_4449091 prefixEnd_4449091 2284522158592757644701509 := by
  unfold tailWord_4449091
  simp only [CollatzResearch.WordTrace]
  refine ⟨162271679924710626093619127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108181119949807084062412751 162271679924710626093619127)
  ·
    refine ⟨243407519887065939140428691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162271679924710626093619127 243407519887065939140428691)
    ·
      refine ⟨365111279830598908710643037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243407519887065939140428691 365111279830598908710643037)
      ·
        refine ⟨136916729936474590766491139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365111279830598908710643037 136916729936474590766491139)
        ·
          refine ⟨205375094904711886149736709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136916729936474590766491139 205375094904711886149736709)
          ·
            refine ⟨38507830294633478653075633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205375094904711886149736709 38507830294633478653075633)
            ·
              refine ⟨28880872720975108989806725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38507830294633478653075633 28880872720975108989806725)
              ·
                refine ⟨5415163635182832935588761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28880872720975108989806725 5415163635182832935588761)
                ·
                  refine ⟨4061372726387124701691571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415163635182832935588761 4061372726387124701691571)
                  ·
                    refine ⟨6092059089580687052537357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061372726387124701691571 6092059089580687052537357)
                    ·
                      refine ⟨2284522158592757644701509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092059089580687052537357 2284522158592757644701509)
                      ·
                        rfl

theorem cell23_4449091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_4449091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449091 prefixEnd_4449091 := by exact prefixLift 4449091
  have htrace : WordTrace (prefixWord ++ tailWord_4449091) baseStart_4449091 baseEnd_4449091 := by
    simpa [prefixWord, tailWord_4449091, baseEnd_4449091] using wordTrace_append hprefix tailTrace_4449091
  have hstable : (prefixWord ++ tailWord_4449091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449091).length < 2 ^ (prefixWord ++ tailWord_4449091).sum := by decide
  have hdescent : baseEnd_4449091 < baseStart_4449091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449107 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 6]
def baseStart_4449107 : Nat := 118140960795 + 4449107 * 2 ^ 59
def prefixEnd_4449107 : Nat := 4983230072969 + 3 ^ 40 * 4449107 * 2
def baseEnd_4449107 : Nat := 761510124761076527367145

theorem tailTrace_4449107 : CollatzResearch.WordTrace tailWord_4449107 prefixEnd_4449107 761510124761076527367145 := by
  unfold tailWord_4449107
  simp only [CollatzResearch.WordTrace]
  refine ⟨162272263492652660826201575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108181508995101773884134383 162272263492652660826201575)
  ·
    refine ⟨243408395238978991239302363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162272263492652660826201575 243408395238978991239302363)
    ·
      refine ⟨365112592858468486858953545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243408395238978991239302363 365112592858468486858953545)
      ·
        refine ⟨273834444643851365144215159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365112592858468486858953545 273834444643851365144215159)
        ·
          refine ⟨410751666965777047716322739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273834444643851365144215159 410751666965777047716322739)
          ·
            refine ⟨616127500448665571574484109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410751666965777047716322739 616127500448665571574484109)
            ·
              refine ⟨231047812668249589340431541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 616127500448665571574484109 231047812668249589340431541)
              ·
                refine ⟨21660732437648399000665457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231047812668249589340431541 21660732437648399000665457)
                ·
                  refine ⟨16245549328236299250499093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21660732437648399000665457 16245549328236299250499093)
                  ·
                    refine ⟨761510124761076527367145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16245549328236299250499093 761510124761076527367145)
                    ·
                      rfl

theorem cell23_4449107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_4449107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449107 prefixEnd_4449107 := by exact prefixLift 4449107
  have htrace : WordTrace (prefixWord ++ tailWord_4449107) baseStart_4449107 baseEnd_4449107 := by
    simpa [prefixWord, tailWord_4449107, baseEnd_4449107] using wordTrace_append hprefix tailTrace_4449107
  have hstable : (prefixWord ++ tailWord_4449107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449107).length < 2 ^ (prefixWord ++ tailWord_4449107).sum := by decide
  have hdescent : baseEnd_4449107 < baseStart_4449107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449131 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 6, 2, 2]
def baseStart_4449131 : Nat := 118140960795 + 4449131 * 2 ^ 59
def prefixEnd_4449131 : Nat := 4983230072969 + 3 ^ 40 * 4449131 * 2
def baseEnd_4449131 : Nat := 2284542697818937488201325

theorem tailTrace_4449131 : CollatzResearch.WordTrace tailWord_4449131 prefixEnd_4449131 2284542697818937488201325 := by
  unfold tailWord_4449131
  simp only [CollatzResearch.WordTrace]
  refine ⟨162273138844565712925075247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108182092563043808616716831 162273138844565712925075247)
  ·
    refine ⟨243409708266848569387612871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162273138844565712925075247 243409708266848569387612871)
    ·
      refine ⟨365114562400272854081419307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243409708266848569387612871 365114562400272854081419307)
      ·
        refine ⟨547671843600409281122128961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365114562400272854081419307 547671843600409281122128961)
        ·
          refine ⟨410753882700306960841596721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547671843600409281122128961 410753882700306960841596721)
          ·
            refine ⟨308065412025230220631197541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410753882700306960841596721 308065412025230220631197541)
            ·
              refine ⟨57762264754730666368349539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308065412025230220631197541 57762264754730666368349539)
              ·
                refine ⟨86643397132095999552524309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57762264754730666368349539 86643397132095999552524309)
                ·
                  refine ⟨4061409240566999979024577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86643397132095999552524309 4061409240566999979024577)
                  ·
                    refine ⟨3046056930425249984268433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061409240566999979024577 3046056930425249984268433)
                    ·
                      refine ⟨2284542697818937488201325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046056930425249984268433 2284542697818937488201325)
                      ·
                        rfl

theorem cell23_4449131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 2, 2].length) (baseStart_4449131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449131 prefixEnd_4449131 := by exact prefixLift 4449131
  have htrace : WordTrace (prefixWord ++ tailWord_4449131) baseStart_4449131 baseEnd_4449131 := by
    simpa [prefixWord, tailWord_4449131, baseEnd_4449131] using wordTrace_append hprefix tailTrace_4449131
  have hstable : (prefixWord ++ tailWord_4449131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449131).length < 2 ^ (prefixWord ++ tailWord_4449131).sum := by decide
  have hdescent : baseEnd_4449131 < baseStart_4449131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449147 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_4449147 : Nat := 118140960795 + 4449147 * 2 ^ 59
def prefixEnd_4449147 : Nat := 4983230072969 + 3 ^ 40 * 4449147 * 2
def baseEnd_4449147 : Nat := 2284550913509409425601251

theorem tailTrace_4449147 : CollatzResearch.WordTrace tailWord_4449147 prefixEnd_4449147 2284550913509409425601251 := by
  unfold tailWord_4449147
  simp only [CollatzResearch.WordTrace]
  refine ⟨162273722412507747657657695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108182481608338498438438463 162273722412507747657657695)
  ·
    refine ⟨243410583618761621486486543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162273722412507747657657695 243410583618761621486486543)
    ·
      refine ⟨365115875428142432229729815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243410583618761621486486543 365115875428142432229729815)
      ·
        refine ⟨547673813142213648344594723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365115875428142432229729815 547673813142213648344594723)
        ·
          refine ⟨821510719713320472516892085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547673813142213648344594723 821510719713320472516892085)
          ·
            refine ⟨77016629973123794298458633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 821510719713320472516892085 77016629973123794298458633)
            ·
              refine ⟨57762472479842845723843975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77016629973123794298458633 57762472479842845723843975)
              ·
                refine ⟨86643708719764268585765963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57762472479842845723843975 86643708719764268585765963)
                ·
                  refine ⟨129965563079646402878648945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86643708719764268585765963 129965563079646402878648945)
                  ·
                    refine ⟨97474172309734802158986709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129965563079646402878648945 97474172309734802158986709)
                    ·
                      refine ⟨2284550913509409425601251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97474172309734802158986709 2284550913509409425601251)
                      ·
                        rfl

theorem cell23_4449147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_4449147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449147 prefixEnd_4449147 := by exact prefixLift 4449147
  have htrace : WordTrace (prefixWord ++ tailWord_4449147) baseStart_4449147 baseEnd_4449147 := by
    simpa [prefixWord, tailWord_4449147, baseEnd_4449147] using wordTrace_append hprefix tailTrace_4449147
  have hstable : (prefixWord ++ tailWord_4449147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449147).length < 2 ^ (prefixWord ++ tailWord_4449147).sum := by decide
  have hdescent : baseEnd_4449147 < baseStart_4449147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449164 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4449164 : Nat := 118140960795 + 4449164 * 2 ^ 59
def prefixEnd_4449164 : Nat := 4983230072969 + 3 ^ 40 * 4449164 * 2
def baseEnd_4449164 : Nat := 2284559642680535859088673

theorem tailTrace_4449164 : CollatzResearch.WordTrace tailWord_4449164 prefixEnd_4449164 2284559642680535859088673 := by
  unfold tailWord_4449164
  simp only [CollatzResearch.WordTrace]
  refine ⟨81137171226723079780513273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108182894968964106374017697 81137171226723079780513273)
  ·
    refine ⟨60852878420042309835384955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81137171226723079780513273 60852878420042309835384955)
    ·
      refine ⟨91279317630063464753077433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60852878420042309835384955 91279317630063464753077433)
      ·
        refine ⟨68459488222547598564808075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91279317630063464753077433 68459488222547598564808075)
        ·
          refine ⟨102689232333821397847212113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68459488222547598564808075 102689232333821397847212113)
          ·
            refine ⟨77016924250366048385409085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102689232333821397847212113 77016924250366048385409085)
            ·
              refine ⟨28881346593887268144528407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77016924250366048385409085 28881346593887268144528407)
              ·
                refine ⟨43322019890830902216792611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28881346593887268144528407 43322019890830902216792611)
                ·
                  refine ⟨64983029836246353325188917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43322019890830902216792611 64983029836246353325188917)
                  ·
                    refine ⟨6092159047148095624236461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64983029836246353325188917 6092159047148095624236461)
                    ·
                      refine ⟨2284559642680535859088673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092159047148095624236461 2284559642680535859088673)
                      ·
                        rfl

theorem cell23_4449164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4449164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449164 prefixEnd_4449164 := by exact prefixLift 4449164
  have htrace : WordTrace (prefixWord ++ tailWord_4449164) baseStart_4449164 baseEnd_4449164 := by
    simpa [prefixWord, tailWord_4449164, baseEnd_4449164] using wordTrace_append hprefix tailTrace_4449164
  have hstable : (prefixWord ++ tailWord_4449164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449164).length < 2 ^ (prefixWord ++ tailWord_4449164).sum := by decide
  have hdescent : baseEnd_4449164 < baseStart_4449164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449231 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 3, 4]
def baseStart_4449231 : Nat := 118140960795 + 4449231 * 2 ^ 59
def prefixEnd_4449231 : Nat := 4983230072969 + 3 ^ 40 * 4449231 * 2
def baseEnd_4449231 : Nat := 761531348628129032316955

theorem tailTrace_4449231 : CollatzResearch.WordTrace tailWord_4449231 prefixEnd_4449231 761531348628129032316955 := by
  unfold tailWord_4449231
  simp only [CollatzResearch.WordTrace]
  refine ⟨162276786144203430003715547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108184524096135620002477031 162276786144203430003715547)
  ·
    refine ⟨243415179216305145005573321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162276786144203430003715547 243415179216305145005573321)
    ·
      refine ⟨182561384412228858754179991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243415179216305145005573321 182561384412228858754179991)
      ·
        refine ⟨273842076618343288131269987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182561384412228858754179991 273842076618343288131269987)
        ·
          refine ⟨410763114927514932196904981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273842076618343288131269987 410763114927514932196904981)
          ·
            refine ⟨19254521012227262446729921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 410763114927514932196904981 19254521012227262446729921)
            ·
              refine ⟨14440890759170446835047441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19254521012227262446729921 14440890759170446835047441)
              ·
                refine ⟨10830668069377835126285581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14440890759170446835047441 10830668069377835126285581)
                ·
                  refine ⟨4061500526016688172357093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10830668069377835126285581 4061500526016688172357093)
                  ·
                    refine ⟨761531348628129032316955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061500526016688172357093 761531348628129032316955)
                    ·
                      rfl

theorem cell23_4449231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_4449231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449231 prefixEnd_4449231 := by exact prefixLift 4449231
  have htrace : WordTrace (prefixWord ++ tailWord_4449231) baseStart_4449231 baseEnd_4449231 := by
    simpa [prefixWord, tailWord_4449231, baseEnd_4449231] using wordTrace_append hprefix tailTrace_4449231
  have hstable : (prefixWord ++ tailWord_4449231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449231).length < 2 ^ (prefixWord ++ tailWord_4449231).sum := by decide
  have hdescent : baseEnd_4449231 < baseStart_4449231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449238 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4449238 : Nat := 118140960795 + 4449238 * 2 ^ 59
def prefixEnd_4449238 : Nat := 4983230072969 + 3 ^ 40 * 4449238 * 2
def baseEnd_4449238 : Nat := 2284597640248968569563333

theorem tailTrace_4449238 : CollatzResearch.WordTrace tailWord_4449238 prefixEnd_4449238 2284597640248968569563333 := by
  unfold tailWord_4449238
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142315090948629387451273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108184694303452046799480245 10142315090948629387451273)
  ·
    refine ⟨7606736318211472040588455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10142315090948629387451273 7606736318211472040588455)
    ·
      refine ⟨11410104477317208060882683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7606736318211472040588455 11410104477317208060882683)
      ·
        refine ⟨17115156715975812091324025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11410104477317208060882683 17115156715975812091324025)
        ·
          refine ⟨12836367536981859068493019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17115156715975812091324025 12836367536981859068493019)
          ·
            refine ⟨19254551305472788602739529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836367536981859068493019 19254551305472788602739529)
            ·
              refine ⟨14440913479104591452054647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19254551305472788602739529 14440913479104591452054647)
              ·
                refine ⟨21661370218656887178081971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14440913479104591452054647 21661370218656887178081971)
                ·
                  refine ⟨32492055327985330767122957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21661370218656887178081971 32492055327985330767122957)
                  ·
                    refine ⟨12184520747994499037671109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32492055327985330767122957 12184520747994499037671109)
                    ·
                      refine ⟨2284597640248968569563333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12184520747994499037671109 2284597640248968569563333)
                      ·
                        rfl

theorem cell23_4449238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4449238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449238 prefixEnd_4449238 := by exact prefixLift 4449238
  have htrace : WordTrace (prefixWord ++ tailWord_4449238) baseStart_4449238 baseEnd_4449238 := by
    simpa [prefixWord, tailWord_4449238, baseEnd_4449238] using wordTrace_append hprefix tailTrace_4449238
  have hstable : (prefixWord ++ tailWord_4449238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449238).length < 2 ^ (prefixWord ++ tailWord_4449238).sum := by decide
  have hdescent : baseEnd_4449238 < baseStart_4449238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449241 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_4449241 : Nat := 118140960795 + 4449241 * 2 ^ 59
def prefixEnd_4449241 : Nat := 4983230072969 + 3 ^ 40 * 4449241 * 2
def baseEnd_4449241 : Nat := 2284599180690932057825819

theorem tailTrace_4449241 : CollatzResearch.WordTrace tailWord_4449241 prefixEnd_4449241 2284599180690932057825819 := by
  unfold tailWord_4449241
  simp only [CollatzResearch.WordTrace]
  refine ⟨162277150874167201711579577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108184767249444801141053051 162277150874167201711579577)
  ·
    refine ⟨121707863155625401283684683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162277150874167201711579577 121707863155625401283684683)
    ·
      refine ⟨182561794733438101925527025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121707863155625401283684683 182561794733438101925527025)
      ·
        refine ⟨136921346050078576444145269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182561794733438101925527025 136921346050078576444145269)
        ·
          refine ⟨12836376192194866541638619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136921346050078576444145269 12836376192194866541638619)
          ·
            refine ⟨19254564288292299812457929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836376192194866541638619 19254564288292299812457929)
            ·
              refine ⟨14440923216219224859343447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19254564288292299812457929 14440923216219224859343447)
              ·
                refine ⟨21661384824328837289015171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14440923216219224859343447 21661384824328837289015171)
                ·
                  refine ⟨32492077236493255933522757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21661384824328837289015171 32492077236493255933522757)
                  ·
                    refine ⟨6092264481842485487535517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32492077236493255933522757 6092264481842485487535517)
                    ·
                      refine ⟨2284599180690932057825819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092264481842485487535517 2284599180690932057825819)
                      ·
                        rfl

theorem cell23_4449241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_4449241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449241 prefixEnd_4449241 := by exact prefixLift 4449241
  have htrace : WordTrace (prefixWord ++ tailWord_4449241) baseStart_4449241 baseEnd_4449241 := by
    simpa [prefixWord, tailWord_4449241, baseEnd_4449241] using wordTrace_append hprefix tailTrace_4449241
  have hstable : (prefixWord ++ tailWord_4449241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449241).length < 2 ^ (prefixWord ++ tailWord_4449241).sum := by decide
  have hdescent : baseEnd_4449241 < baseStart_4449241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449258 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_4449258 : Nat := 118140960795 + 4449258 * 2 ^ 59
def prefixEnd_4449258 : Nat := 4983230072969 + 3 ^ 40 * 4449258 * 2
def baseEnd_4449258 : Nat := 2284607909862058491313241

theorem tailTrace_4449258 : CollatzResearch.WordTrace tailWord_4449258 prefixEnd_4449258 2284607909862058491313241 := by
  unfold tailWord_4449258
  simp only [CollatzResearch.WordTrace]
  refine ⟨40569442728776403403737107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108185180610070409076632285 40569442728776403403737107)
  ·
    refine ⟨60854164093164605105605661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40569442728776403403737107 60854164093164605105605661)
    ·
      refine ⟨22820311534936726914602123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60854164093164605105605661 22820311534936726914602123)
      ·
        refine ⟨34230467302405090371903185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22820311534936726914602123 34230467302405090371903185)
        ·
          refine ⟨25672850476803817778927389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34230467302405090371903185 25672850476803817778927389)
          ·
            refine ⟨9627318928801431667097771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25672850476803817778927389 9627318928801431667097771)
            ·
              refine ⟨14440978393202147500646657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627318928801431667097771 14440978393202147500646657)
              ·
                refine ⟨10830733794901610625484993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14440978393202147500646657 10830733794901610625484993)
                ·
                  refine ⟨8123050346176207969113745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10830733794901610625484993 8123050346176207969113745)
                  ·
                    refine ⟨6092287759632155976835309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8123050346176207969113745 6092287759632155976835309)
                    ·
                      refine ⟨2284607909862058491313241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6092287759632155976835309 2284607909862058491313241)
                      ·
                        rfl

theorem cell23_4449258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_4449258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449258 prefixEnd_4449258 := by exact prefixLift 4449258
  have htrace : WordTrace (prefixWord ++ tailWord_4449258) baseStart_4449258 baseEnd_4449258 := by
    simpa [prefixWord, tailWord_4449258, baseEnd_4449258] using wordTrace_append hprefix tailTrace_4449258
  have hstable : (prefixWord ++ tailWord_4449258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449258).length < 2 ^ (prefixWord ++ tailWord_4449258).sum := by decide
  have hdescent : baseEnd_4449258 < baseStart_4449258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449291 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 3, 5]
def baseStart_4449291 : Nat := 118140960795 + 4449291 * 2 ^ 59
def prefixEnd_4449291 : Nat := 4983230072969 + 3 ^ 40 * 4449291 * 2
def baseEnd_4449291 : Nat := 761541618241218954066863

theorem tailTrace_4449291 : CollatzResearch.WordTrace tailWord_4449291 prefixEnd_4449291 761541618241218954066863 := by
  unfold tailWord_4449291
  simp only [CollatzResearch.WordTrace]
  refine ⟨162278974523986060250899727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108185983015990706833933151 162278974523986060250899727)
  ·
    refine ⟨243418461785979090376349591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162278974523986060250899727 243418461785979090376349591)
    ·
      refine ⟨365127692678968635564524387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243418461785979090376349591 365127692678968635564524387)
      ·
        refine ⟨547691539018452953346786581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365127692678968635564524387 547691539018452953346786581)
        ·
          refine ⟨25673040891489982188130621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 547691539018452953346786581 25673040891489982188130621)
          ·
            refine ⟨9627390334308743320548983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25673040891489982188130621 9627390334308743320548983)
            ·
              refine ⟨14441085501463114980823475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627390334308743320548983 14441085501463114980823475)
              ·
                refine ⟨21661628252194672471235213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14441085501463114980823475 21661628252194672471235213)
                ·
                  refine ⟨8123110594573002176713205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21661628252194672471235213 8123110594573002176713205)
                  ·
                    refine ⟨761541618241218954066863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8123110594573002176713205 761541618241218954066863)
                    ·
                      rfl

theorem cell23_4449291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].length) (baseStart_4449291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449291 prefixEnd_4449291 := by exact prefixLift 4449291
  have htrace : WordTrace (prefixWord ++ tailWord_4449291) baseStart_4449291 baseEnd_4449291 := by
    simpa [prefixWord, tailWord_4449291, baseEnd_4449291] using wordTrace_append hprefix tailTrace_4449291
  have hstable : (prefixWord ++ tailWord_4449291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449291).length < 2 ^ (prefixWord ++ tailWord_4449291).sum := by decide
  have hdescent : baseEnd_4449291 < baseStart_4449291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449338 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_4449338 : Nat := 118140960795 + 4449338 * 2 ^ 59
def prefixEnd_4449338 : Nat := 4983230072969 + 3 ^ 40 * 4449338 * 2
def baseEnd_4449338 : Nat := 761549662771472726104291

theorem tailTrace_4449338 : CollatzResearch.WordTrace tailWord_4449338 prefixEnd_4449338 761549662771472726104291 := by
  unfold tailWord_4449338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570172188703946819465167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108187125836543858185240445 40570172188703946819465167)
  ·
    refine ⟨60855258283055920229197751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40570172188703946819465167 60855258283055920229197751)
    ·
      refine ⟨91282887424583880343796627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60855258283055920229197751 91282887424583880343796627)
      ·
        refine ⟨136924331136875820515694941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91282887424583880343796627 136924331136875820515694941)
        ·
          refine ⟨51346624176328432693385603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136924331136875820515694941 51346624176328432693385603)
          ·
            refine ⟨77019936264492649040078405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51346624176328432693385603 77019936264492649040078405)
            ·
              refine ⟨14441238049592371695014701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77019936264492649040078405 14441238049592371695014701)
              ·
                refine ⟨5415464268597139385630513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14441238049592371695014701 5415464268597139385630513)
                ·
                  refine ⟨4061598201447854539222885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415464268597139385630513 4061598201447854539222885)
                  ·
                    refine ⟨761549662771472726104291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061598201447854539222885 761549662771472726104291)
                    ·
                      rfl

theorem cell23_4449338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_4449338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449338 prefixEnd_4449338 := by exact prefixLift 4449338
  have htrace : WordTrace (prefixWord ++ tailWord_4449338) baseStart_4449338 baseEnd_4449338 := by
    simpa [prefixWord, tailWord_4449338, baseEnd_4449338] using wordTrace_append hprefix tailTrace_4449338
  have hstable : (prefixWord ++ tailWord_4449338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449338).length < 2 ^ (prefixWord ++ tailWord_4449338).sum := by decide
  have hdescent : baseEnd_4449338 < baseStart_4449338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449362 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_4449362 : Nat := 118140960795 + 4449362 * 2 ^ 59
def prefixEnd_4449362 : Nat := 4983230072969 + 3 ^ 40 * 4449362 * 2
def baseEnd_4449362 : Nat := 2284661311850126084412763

theorem tailTrace_4449362 : CollatzResearch.WordTrace tailWord_4449362 prefixEnd_4449362 2284661311850126084412763 := by
  unfold tailWord_4449362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570391026682209844183585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108187709404485892917822893 40570391026682209844183585)
  ·
    refine ⟨30427793270011657383137689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40570391026682209844183585 30427793270011657383137689)
    ·
      refine ⟨22820844952508743037353267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30427793270011657383137689 22820844952508743037353267)
      ·
        refine ⟨34231267428763114556029901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22820844952508743037353267 34231267428763114556029901)
        ·
          refine ⟨12836725285786167958511213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34231267428763114556029901 12836725285786167958511213)
          ·
            refine ⟨4813771982169812984441705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12836725285786167958511213 4813771982169812984441705)
            ·
              refine ⟨3610328986627359738331279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813771982169812984441705 3610328986627359738331279)
              ·
                refine ⟨5415493479941039607496919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610328986627359738331279 5415493479941039607496919)
                ·
                  refine ⟨8123240219911559411245379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415493479941039607496919 8123240219911559411245379)
                  ·
                    refine ⟨12184860329867339116868069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8123240219911559411245379 12184860329867339116868069)
                    ·
                      refine ⟨2284661311850126084412763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12184860329867339116868069 2284661311850126084412763)
                      ·
                        rfl

theorem cell23_4449362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_4449362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449362 prefixEnd_4449362 := by exact prefixLift 4449362
  have htrace : WordTrace (prefixWord ++ tailWord_4449362) baseStart_4449362 baseEnd_4449362 := by
    simpa [prefixWord, tailWord_4449362, baseEnd_4449362] using wordTrace_append hprefix tailTrace_4449362
  have hstable : (prefixWord ++ tailWord_4449362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449362).length < 2 ^ (prefixWord ++ tailWord_4449362).sum := by decide
  have hdescent : baseEnd_4449362 < baseStart_4449362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449422 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4449422 : Nat := 118140960795 + 4449422 * 2 ^ 59
def prefixEnd_4449422 : Nat := 4983230072969 + 3 ^ 40 * 4449422 * 2
def baseEnd_4449422 : Nat := 2284692120689395849662487

theorem tailTrace_4449422 : CollatzResearch.WordTrace tailWord_4449422 prefixEnd_4449422 2284692120689395849662487 := by
  unfold tailWord_4449422
  simp only [CollatzResearch.WordTrace]
  refine ⟨20285469060813933702989815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108189168324340979749279013 20285469060813933702989815)
  ·
    refine ⟨30428203591220900554484723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20285469060813933702989815 30428203591220900554484723)
    ·
      refine ⟨45642305386831350831727085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30428203591220900554484723 45642305386831350831727085)
      ·
        refine ⟨17115864520061756561897657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45642305386831350831727085 17115864520061756561897657)
        ·
          refine ⟨12836898390046317421423243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17115864520061756561897657 12836898390046317421423243)
          ·
            refine ⟨19255347585069476132134865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836898390046317421423243 19255347585069476132134865)
            ·
              refine ⟨14441510688802107099101149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19255347585069476132134865 14441510688802107099101149)
              ·
                refine ⟨5415566508300790162162931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14441510688802107099101149 5415566508300790162162931)
                ·
                  refine ⟨8123349762451185243244397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415566508300790162162931 8123349762451185243244397)
                  ·
                    refine ⟨3046256160919194466216649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8123349762451185243244397 3046256160919194466216649)
                    ·
                      refine ⟨2284692120689395849662487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046256160919194466216649 2284692120689395849662487)
                      ·
                        rfl

theorem cell23_4449422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4449422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449422 prefixEnd_4449422 := by exact prefixLift 4449422
  have htrace : WordTrace (prefixWord ++ tailWord_4449422) baseStart_4449422 baseEnd_4449422 := by
    simpa [prefixWord, tailWord_4449422, baseEnd_4449422] using wordTrace_append hprefix tailTrace_4449422
  have hstable : (prefixWord ++ tailWord_4449422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449422).length < 2 ^ (prefixWord ++ tailWord_4449422).sum := by decide
  have hdescent : baseEnd_4449422 < baseStart_4449422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449471 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 7]
def baseStart_4449471 : Nat := 118140960795 + 4449471 * 2 ^ 59
def prefixEnd_4449471 : Nat := 4983230072969 + 3 ^ 40 * 4449471 * 2
def baseEnd_4449471 : Nat := 761572427080488719316587

theorem tailTrace_4449471 : CollatzResearch.WordTrace tailWord_4449471 prefixEnd_4449471 761572427080488719316587 := by
  unfold tailWord_4449471
  simp only [CollatzResearch.WordTrace]
  refine ⟨162285539663333950992452267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108190359775555967328301511 162285539663333950992452267)
  ·
    refine ⟨243428309495000926488678401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162285539663333950992452267 243428309495000926488678401)
    ·
      refine ⟨182571232121250694866508801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243428309495000926488678401 182571232121250694866508801)
      ·
        refine ⟨136928424090938021149881601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182571232121250694866508801 136928424090938021149881601)
        ·
          refine ⟨102696318068203515862411201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136928424090938021149881601 102696318068203515862411201)
          ·
            refine ⟨77022238551152636896808401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102696318068203515862411201 77022238551152636896808401)
            ·
              refine ⟨57766678913364477672606301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77022238551152636896808401 57766678913364477672606301)
              ·
                refine ⟨21662504592511679127227363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57766678913364477672606301 21662504592511679127227363)
                ·
                  refine ⟨32493756888767518690841045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21662504592511679127227363 32493756888767518690841045)
                  ·
                    refine ⟨761572427080488719316587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32493756888767518690841045 761572427080488719316587)
                    ·
                      rfl

theorem cell23_4449471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_4449471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449471 prefixEnd_4449471 := by exact prefixLift 4449471
  have htrace : WordTrace (prefixWord ++ tailWord_4449471) baseStart_4449471 baseEnd_4449471 := by
    simpa [prefixWord, tailWord_4449471, baseEnd_4449471] using wordTrace_append hprefix tailTrace_4449471
  have hstable : (prefixWord ++ tailWord_4449471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449471).length < 2 ^ (prefixWord ++ tailWord_4449471).sum := by decide
  have hdescent : baseEnd_4449471 < baseStart_4449471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449508 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_4449508 : Nat := 118140960795 + 4449508 * 2 ^ 59
def prefixEnd_4449508 : Nat := 4983230072969 + 3 ^ 40 * 4449508 * 2
def baseEnd_4449508 : Nat := 2284736280025682513187091

theorem tailTrace_4449508 : CollatzResearch.WordTrace tailWord_4449508 prefixEnd_4449508 2284736280025682513187091 := by
  unfold tailWord_4449508
  simp only [CollatzResearch.WordTrace]
  refine ⟨81143444582099953155774589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108191259442799937541032785 81143444582099953155774589)
  ·
    refine ⟨30428791718287482433415471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81143444582099953155774589 30428791718287482433415471)
    ·
      refine ⟨45643187577431223650123207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30428791718287482433415471 45643187577431223650123207)
      ·
        refine ⟨68464781366146835475184811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45643187577431223650123207 68464781366146835475184811)
        ·
          refine ⟨102697172049220253212777217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68464781366146835475184811 102697172049220253212777217)
          ·
            refine ⟨77022879036915189909582913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102697172049220253212777217 77022879036915189909582913)
            ·
              refine ⟨57767159277686392432187185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77022879036915189909582913 57767159277686392432187185)
              ·
                refine ⟨43325369458264794324140389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57767159277686392432187185 43325369458264794324140389)
                ·
                  refine ⟨8123506773424648935776323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43325369458264794324140389 8123506773424648935776323)
                  ·
                    refine ⟨12185260160136973403664485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8123506773424648935776323 12185260160136973403664485)
                    ·
                      refine ⟨2284736280025682513187091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12185260160136973403664485 2284736280025682513187091)
                      ·
                        rfl

theorem cell23_4449508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_4449508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449508 prefixEnd_4449508 := by exact prefixLift 4449508
  have htrace : WordTrace (prefixWord ++ tailWord_4449508) baseStart_4449508 baseEnd_4449508 := by
    simpa [prefixWord, tailWord_4449508, baseEnd_4449508] using wordTrace_append hprefix tailTrace_4449508
  have hstable : (prefixWord ++ tailWord_4449508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449508).length < 2 ^ (prefixWord ++ tailWord_4449508).sum := by decide
  have hdescent : baseEnd_4449508 < baseStart_4449508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449522 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_4449522 : Nat := 118140960795 + 4449522 * 2 ^ 59
def prefixEnd_4449522 : Nat := 4983230072969 + 3 ^ 40 * 4449522 * 2
def baseEnd_4449522 : Nat := 761581156251615152804009

theorem tailTrace_4449522 : CollatzResearch.WordTrace tailWord_4449522 prefixEnd_4449522 761581156251615152804009 := by
  unfold tailWord_4449522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40571849946537296675639705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108191599857432791135039213 40571849946537296675639705)
  ·
    refine ⟨30428887459902972506729779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40571849946537296675639705 30428887459902972506729779)
    ·
      refine ⟨45643331189854458760094669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30428887459902972506729779 45643331189854458760094669)
      ·
        refine ⟨17116249196195422035035501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45643331189854458760094669 17116249196195422035035501)
        ·
          refine ⟨6418593448573283263138313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17116249196195422035035501 6418593448573283263138313)
          ·
            refine ⟨4813945086429962447353735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418593448573283263138313 4813945086429962447353735)
            ·
              refine ⟨7220917629644943671030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813945086429962447353735 7220917629644943671030603)
              ·
                refine ⟨10831376444467415506545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7220917629644943671030603 10831376444467415506545905)
                ·
                  refine ⟨8123532333350561629909429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10831376444467415506545905 8123532333350561629909429)
                  ·
                    refine ⟨761581156251615152804009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8123532333350561629909429 761581156251615152804009)
                    ·
                      rfl

theorem cell23_4449522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_4449522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449522 prefixEnd_4449522 := by exact prefixLift 4449522
  have htrace : WordTrace (prefixWord ++ tailWord_4449522) baseStart_4449522 baseEnd_4449522 := by
    simpa [prefixWord, tailWord_4449522, baseEnd_4449522] using wordTrace_append hprefix tailTrace_4449522
  have hstable : (prefixWord ++ tailWord_4449522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449522).length < 2 ^ (prefixWord ++ tailWord_4449522).sum := by decide
  have hdescent : baseEnd_4449522 < baseStart_4449522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449548 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 8]
def baseStart_4449548 : Nat := 118140960795 + 4449548 * 2 ^ 59
def prefixEnd_4449548 : Nat := 4983230072969 + 3 ^ 40 * 4449548 * 2
def baseEnd_4449548 : Nat := 253861868805762484076323

theorem tailTrace_4449548 : CollatzResearch.WordTrace tailWord_4449548 prefixEnd_4449548 253861868805762484076323 := by
  unfold tailWord_4449548
  simp only [CollatzResearch.WordTrace]
  refine ⟨81144174042027496571502649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108192232056036662095336865 81144174042027496571502649)
  ·
    refine ⟨60858130531520622428626987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81144174042027496571502649 60858130531520622428626987)
    ·
      refine ⟨91287195797280933642940481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60858130531520622428626987 91287195797280933642940481)
      ·
        refine ⟨68465396847960700232205361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91287195797280933642940481 68465396847960700232205361)
        ·
          refine ⟨51349047635970525174154021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68465396847960700232205361 51349047635970525174154021)
          ·
            refine ⟨9627946431744473470153879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51349047635970525174154021 9627946431744473470153879)
            ·
              refine ⟨14441919647616710205230819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627946431744473470153879 14441919647616710205230819)
              ·
                refine ⟨21662879471425065307846229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14441919647616710205230819 21662879471425065307846229)
                ·
                  refine ⟨253861868805762484076323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21662879471425065307846229 253861868805762484076323)
                  ·
                    rfl

theorem cell23_4449548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_4449548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449548 prefixEnd_4449548 := by exact prefixLift 4449548
  have htrace : WordTrace (prefixWord ++ tailWord_4449548) baseStart_4449548 baseEnd_4449548 := by
    simpa [prefixWord, tailWord_4449548, baseEnd_4449548] using wordTrace_append hprefix tailTrace_4449548
  have hstable : (prefixWord ++ tailWord_4449548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449548).length < 2 ^ (prefixWord ++ tailWord_4449548).sum := by decide
  have hdescent : baseEnd_4449548 < baseStart_4449548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449632 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_4449632 : Nat := 118140960795 + 4449632 * 2 ^ 59
def prefixEnd_4449632 : Nat := 4983230072969 + 3 ^ 40 * 4449632 * 2
def baseEnd_4449632 : Nat := 2284799951626840028036521

theorem tailTrace_4449632 : CollatzResearch.WordTrace tailWord_4449632 prefixEnd_4449632 2284799951626840028036521 := by
  unfold tailWord_4449632
  simp only [CollatzResearch.WordTrace]
  refine ⟨81145705907875337744531575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108194274543833783659375433 81145705907875337744531575)
  ·
    refine ⟨121718558861813006616797363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81145705907875337744531575 121718558861813006616797363)
    ·
      refine ⟨182577838292719509925196045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121718558861813006616797363 182577838292719509925196045)
      ·
        refine ⟨68466689359769816221948517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182577838292719509925196045 68466689359769816221948517)
        ·
          refine ⟨12837504254956840541615347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68466689359769816221948517 12837504254956840541615347)
          ·
            refine ⟨19256256382435260812423021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12837504254956840541615347 19256256382435260812423021)
            ·
              refine ⟨7221096143413222804658633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19256256382435260812423021 7221096143413222804658633)
              ·
                refine ⟨5415822107559917103493975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7221096143413222804658633 5415822107559917103493975)
                ·
                  refine ⟨8123733161339875655240963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415822107559917103493975 8123733161339875655240963)
                  ·
                    refine ⟨12185599742009813482861445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8123733161339875655240963 12185599742009813482861445)
                    ·
                      refine ⟨2284799951626840028036521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12185599742009813482861445 2284799951626840028036521)
                      ·
                        rfl

theorem cell23_4449632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_4449632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449632 prefixEnd_4449632 := by exact prefixLift 4449632
  have htrace : WordTrace (prefixWord ++ tailWord_4449632) baseStart_4449632 baseEnd_4449632 := by
    simpa [prefixWord, tailWord_4449632, baseEnd_4449632] using wordTrace_append hprefix tailTrace_4449632
  have hstable : (prefixWord ++ tailWord_4449632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449632).length < 2 ^ (prefixWord ++ tailWord_4449632).sum := by decide
  have hdescent : baseEnd_4449632 < baseStart_4449632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449642 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_4449642 : Nat := 118140960795 + 4449642 * 2 ^ 59
def prefixEnd_4449642 : Nat := 4983230072969 + 3 ^ 40 * 4449642 * 2
def baseEnd_4449642 : Nat := 761601695477794996303825

theorem tailTrace_4449642 : CollatzResearch.WordTrace tailWord_4449642 prefixEnd_4449642 761601695477794996303825 := by
  unfold tailWord_4449642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40572944136428611799231795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108194517697142964797951453 40572944136428611799231795)
  ·
    refine ⟨60859416204642917698847693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40572944136428611799231795 60859416204642917698847693)
    ·
      refine ⟨22822281076741094137067885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60859416204642917698847693 22822281076741094137067885)
      ·
        refine ⟨8558355403777910301400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22822281076741094137067885 8558355403777910301400457)
        ·
          refine ⟨6418766552833432726050343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8558355403777910301400457 6418766552833432726050343)
          ·
            refine ⟨9628149829250149089075515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418766552833432726050343 9628149829250149089075515)
            ·
              refine ⟨14442224743875223633613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9628149829250149089075515 14442224743875223633613273)
              ·
                refine ⟨10831668557906417725209955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14442224743875223633613273 10831668557906417725209955)
                ·
                  refine ⟨16247502836859626587814933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10831668557906417725209955 16247502836859626587814933)
                  ·
                    refine ⟨761601695477794996303825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16247502836859626587814933 761601695477794996303825)
                    ·
                      rfl

theorem cell23_4449642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_4449642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449642 prefixEnd_4449642 := by exact prefixLift 4449642
  have htrace : WordTrace (prefixWord ++ tailWord_4449642) baseStart_4449642 baseEnd_4449642 := by
    simpa [prefixWord, tailWord_4449642, baseEnd_4449642] using wordTrace_append hprefix tailTrace_4449642
  have hstable : (prefixWord ++ tailWord_4449642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449642).length < 2 ^ (prefixWord ++ tailWord_4449642).sum := by decide
  have hdescent : baseEnd_4449642 < baseStart_4449642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449645 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4449645 : Nat := 118140960795 + 4449645 * 2 ^ 59
def prefixEnd_4449645 : Nat := 4983230072969 + 3 ^ 40 * 4449645 * 2
def baseEnd_4449645 : Nat := 2284806626875348477173961

theorem tailTrace_4449645 : CollatzResearch.WordTrace tailWord_4449645 prefixEnd_4449645 2284806626875348477173961 := by
  unfold tailWord_4449645
  simp only [CollatzResearch.WordTrace]
  refine ⟨162291885964703578709286389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108194590643135719139524259 162291885964703578709286389)
  ·
    refine ⟨15214864309190960503995599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162291885964703578709286389 15214864309190960503995599)
    ·
      refine ⟨22822296463786440755993399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15214864309190960503995599 22822296463786440755993399)
      ·
        refine ⟨34233444695679661133990099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22822296463786440755993399 34233444695679661133990099)
        ·
          refine ⟨51350167043519491700985149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34233444695679661133990099 51350167043519491700985149)
          ·
            refine ⟨19256312641319809387869431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51350167043519491700985149 19256312641319809387869431)
            ·
              refine ⟨28884468961979714081804147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19256312641319809387869431 28884468961979714081804147)
              ·
                refine ⟨43326703442969571122706221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28884468961979714081804147 43326703442969571122706221)
                ·
                  refine ⟨16247513791113589171014833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43326703442969571122706221 16247513791113589171014833)
                  ·
                    refine ⟨12185635343335191878261125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16247513791113589171014833 12185635343335191878261125)
                    ·
                      refine ⟨2284806626875348477173961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12185635343335191878261125 2284806626875348477173961)
                      ·
                        rfl

theorem cell23_4449645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4449645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449645 prefixEnd_4449645 := by exact prefixLift 4449645
  have htrace : WordTrace (prefixWord ++ tailWord_4449645) baseStart_4449645 baseEnd_4449645 := by
    simpa [prefixWord, tailWord_4449645, baseEnd_4449645] using wordTrace_append hprefix tailTrace_4449645
  have hstable : (prefixWord ++ tailWord_4449645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449645).length < 2 ^ (prefixWord ++ tailWord_4449645).sum := by decide
  have hdescent : baseEnd_4449645 < baseStart_4449645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449646 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_4449646 : Nat := 118140960795 + 4449646 * 2 ^ 59
def prefixEnd_4449646 : Nat := 4983230072969 + 3 ^ 40 * 4449646 * 2
def baseEnd_4449646 : Nat := 761602380118667657753819

theorem tailTrace_4449646 : CollatzResearch.WordTrace tailWord_4449646 prefixEnd_4449646 761602380118667657753819 := by
  unfold tailWord_4449646
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286490304712494485009099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108194614958466637253381861 20286490304712494485009099)
  ·
    refine ⟨30429735457068741727513649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20286490304712494485009099 30429735457068741727513649)
    ·
      refine ⟨22822301592801556295635237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30429735457068741727513649 22822301592801556295635237)
      ·
        refine ⟨4279181548650291805431607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22822301592801556295635237 4279181548650291805431607)
        ·
          refine ⟨6418772322975437708147411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279181548650291805431607 6418772322975437708147411)
          ·
            refine ⟨9628158484463156562221117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418772322975437708147411 9628158484463156562221117)
            ·
              refine ⟨3610559431673683710832919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9628158484463156562221117 3610559431673683710832919)
              ·
                refine ⟨5415839147510525566249379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610559431673683710832919 5415839147510525566249379)
                ·
                  refine ⟨8123758721265788349374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415839147510525566249379 8123758721265788349374069)
                  ·
                    refine ⟨761602380118667657753819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8123758721265788349374069 761602380118667657753819)
                    ·
                      rfl

theorem cell23_4449646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_4449646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449646 prefixEnd_4449646 := by exact prefixLift 4449646
  have htrace : WordTrace (prefixWord ++ tailWord_4449646) baseStart_4449646 baseEnd_4449646 := by
    simpa [prefixWord, tailWord_4449646, baseEnd_4449646] using wordTrace_append hprefix tailTrace_4449646
  have hstable : (prefixWord ++ tailWord_4449646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449646).length < 2 ^ (prefixWord ++ tailWord_4449646).sum := by decide
  have hdescent : baseEnd_4449646 < baseStart_4449646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449730 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4449730 : Nat := 118140960795 + 4449730 * 2 ^ 59
def prefixEnd_4449730 : Nat := 4983230072969 + 3 ^ 40 * 4449730 * 2
def baseEnd_4449730 : Nat := 2284850272730980644611071

theorem tailTrace_4449730 : CollatzResearch.WordTrace tailWord_4449730 prefixEnd_4449730 2284850272730980644611071 := by
  unfold tailWord_4449730
  simp only [CollatzResearch.WordTrace]
  refine ⟨40573746542348909556532661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108196657446263758817420429 40573746542348909556532661)
  ·
    refine ⟨3803788738345210270924937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40573746542348909556532661 3803788738345210270924937)
    ·
      refine ⟨2852841553758907703193703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3803788738345210270924937 2852841553758907703193703)
      ·
        refine ⟨4279262330638361554790555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852841553758907703193703 4279262330638361554790555)
        ·
          refine ⟨6418893495957542332185833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279262330638361554790555 6418893495957542332185833)
          ·
            refine ⟨4814170121968156749139375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418893495957542332185833 4814170121968156749139375)
            ·
              refine ⟨7221255182952235123709063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814170121968156749139375 7221255182952235123709063)
              ·
                refine ⟨10831882774428352685563595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221255182952235123709063 10831882774428352685563595)
                ·
                  refine ⟨16247824161642529028345393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10831882774428352685563595 16247824161642529028345393)
                  ·
                    refine ⟨12185868121231896771259045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16247824161642529028345393 12185868121231896771259045)
                    ·
                      refine ⟨2284850272730980644611071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12185868121231896771259045 2284850272730980644611071)
                      ·
                        rfl

theorem cell23_4449730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4449730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449730 prefixEnd_4449730 := by exact prefixLift 4449730
  have htrace : WordTrace (prefixWord ++ tailWord_4449730) baseStart_4449730 baseEnd_4449730 := by
    simpa [prefixWord, tailWord_4449730, baseEnd_4449730] using wordTrace_append hprefix tailTrace_4449730
  have hstable : (prefixWord ++ tailWord_4449730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449730).length < 2 ^ (prefixWord ++ tailWord_4449730).sum := by decide
  have hdescent : baseEnd_4449730 < baseStart_4449730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449732 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4449732 : Nat := 118140960795 + 4449732 * 2 ^ 59
def prefixEnd_4449732 : Nat := 4983230072969 + 3 ^ 40 * 4449732 * 2
def baseEnd_4449732 : Nat := 761617099897429878928687

theorem tailTrace_4449732 : CollatzResearch.WordTrace tailWord_4449732 prefixEnd_4449732 761617099897429878928687 := by
  unfold tailWord_4449732
  simp only [CollatzResearch.WordTrace]
  refine ⟨81147529557694196283851725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108196706076925595045135633 81147529557694196283851725)
  ·
    refine ⟨30430323584135323606444397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81147529557694196283851725 30430323584135323606444397)
    ·
      refine ⟨11411371344050746352416649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30430323584135323606444397 11411371344050746352416649)
      ·
        refine ⟨8558528508038059764312487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11411371344050746352416649 8558528508038059764312487)
        ·
          refine ⟨12837792762057089646468731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558528508038059764312487 12837792762057089646468731)
          ·
            refine ⟨19256689143085634469703097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12837792762057089646468731 19256689143085634469703097)
            ·
              refine ⟨14442516857314225852277323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19256689143085634469703097 14442516857314225852277323)
              ·
                refine ⟨21663775285971338778415985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14442516857314225852277323 21663775285971338778415985)
                ·
                  refine ⟨16247831464478504083811989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21663775285971338778415985 16247831464478504083811989)
                  ·
                    refine ⟨761617099897429878928687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16247831464478504083811989 761617099897429878928687)
                    ·
                      rfl

theorem cell23_4449732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4449732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449732 prefixEnd_4449732 := by exact prefixLift 4449732
  have htrace : WordTrace (prefixWord ++ tailWord_4449732) baseStart_4449732 baseEnd_4449732 := by
    simpa [prefixWord, tailWord_4449732, baseEnd_4449732] using wordTrace_append hprefix tailTrace_4449732
  have hstable : (prefixWord ++ tailWord_4449732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449732).length < 2 ^ (prefixWord ++ tailWord_4449732).sum := by decide
  have hdescent : baseEnd_4449732 < baseStart_4449732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449735 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4449735 : Nat := 118140960795 + 4449735 * 2 ^ 59
def prefixEnd_4449735 : Nat := 4983230072969 + 3 ^ 40 * 4449735 * 2
def baseEnd_4449735 : Nat := 2284852840134253125048547

theorem tailTrace_4449735 : CollatzResearch.WordTrace tailWord_4449735 prefixEnd_4449735 2284852840134253125048547 := by
  unfold tailWord_4449735
  simp only [CollatzResearch.WordTrace]
  refine ⟨162295168534377524080062659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108196779022918349386708439 162295168534377524080062659)
  ·
    refine ⟨243442752801566286120093989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162295168534377524080062659 243442752801566286120093989)
    ·
      refine ⟨45645516150293678647517623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243442752801566286120093989 45645516150293678647517623)
      ·
        refine ⟨68468274225440517971276435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45645516150293678647517623 68468274225440517971276435)
        ·
          refine ⟨102702411338160776956914653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68468274225440517971276435 102702411338160776956914653)
          ·
            refine ⟨38513404251810291358842995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102702411338160776956914653 38513404251810291358842995)
            ·
              refine ⟨57770106377715437038264493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38513404251810291358842995 57770106377715437038264493)
              ·
                refine ⟨21663789891643288889349185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57770106377715437038264493 21663789891643288889349185)
                ·
                  refine ⟨16247842418732466667011889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21663789891643288889349185 16247842418732466667011889)
                  ·
                    refine ⟨12185881814049350000258917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16247842418732466667011889 12185881814049350000258917)
                    ·
                      refine ⟨2284852840134253125048547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12185881814049350000258917 2284852840134253125048547)
                      ·
                        rfl

theorem cell23_4449735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4449735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449735 prefixEnd_4449735 := by exact prefixLift 4449735
  have htrace : WordTrace (prefixWord ++ tailWord_4449735) baseStart_4449735 baseEnd_4449735 := by
    simpa [prefixWord, tailWord_4449735, baseEnd_4449735] using wordTrace_append hprefix tailTrace_4449735
  have hstable : (prefixWord ++ tailWord_4449735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449735).length < 2 ^ (prefixWord ++ tailWord_4449735).sum := by decide
  have hdescent : baseEnd_4449735 < baseStart_4449735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449739 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 2, 2, 2]
def baseStart_4449739 : Nat := 118140960795 + 4449739 * 2 ^ 59
def prefixEnd_4449739 : Nat := 4983230072969 + 3 ^ 40 * 4449739 * 2
def baseEnd_4449739 : Nat := 2284854894056871109398529

theorem tailTrace_4449739 : CollatzResearch.WordTrace tailWord_4449739 prefixEnd_4449739 2284854894056871109398529 := by
  unfold tailWord_4449739
  simp only [CollatzResearch.WordTrace]
  refine ⟨162295314426363032763208271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108196876284242021842138847 162295314426363032763208271)
  ·
    refine ⟨243442971639544549144812407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162295314426363032763208271 243442971639544549144812407)
    ·
      refine ⟨365164457459316823717218611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243442971639544549144812407 365164457459316823717218611)
      ·
        refine ⟨547746686188975235575827917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365164457459316823717218611 547746686188975235575827917)
        ·
          refine ⟨205405007320865713340935469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 547746686188975235575827917 205405007320865713340935469)
          ·
            refine ⟨77026877745324642502850801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205405007320865713340935469 77026877745324642502850801)
            ·
              refine ⟨57770158308993481877138101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77026877745324642502850801 57770158308993481877138101)
              ·
                refine ⟨5415952341468138925981697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57770158308993481877138101 5415952341468138925981697)
                ·
                  refine ⟨4061964256101104194486273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415952341468138925981697 4061964256101104194486273)
                  ·
                    refine ⟨3046473192075828145864705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061964256101104194486273 3046473192075828145864705)
                    ·
                      refine ⟨2284854894056871109398529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046473192075828145864705 2284854894056871109398529)
                      ·
                        rfl

theorem cell23_4449739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2, 2].length) (baseStart_4449739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449739 prefixEnd_4449739 := by exact prefixLift 4449739
  have htrace : WordTrace (prefixWord ++ tailWord_4449739) baseStart_4449739 baseEnd_4449739 := by
    simpa [prefixWord, tailWord_4449739, baseEnd_4449739] using wordTrace_append hprefix tailTrace_4449739
  have hstable : (prefixWord ++ tailWord_4449739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449739).length < 2 ^ (prefixWord ++ tailWord_4449739).sum := by decide
  have hdescent : baseEnd_4449739 < baseStart_4449739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449775 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 4, 5]
def baseStart_4449775 : Nat := 118140960795 + 4449775 * 2 ^ 59
def prefixEnd_4449775 : Nat := 4983230072969 + 3 ^ 40 * 4449775 * 2
def baseEnd_4449775 : Nat := 761624459786810989516121

theorem tailTrace_4449775 : CollatzResearch.WordTrace tailWord_4449775 prefixEnd_4449775 761624459786810989516121 := by
  unfold tailWord_4449775
  simp only [CollatzResearch.WordTrace]
  refine ⟨162296627454232610911518779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108197751636155073941012519 162296627454232610911518779)
  ·
    refine ⟨243444941181348916367278169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162296627454232610911518779 243444941181348916367278169)
    ·
      refine ⟨182583705886011687275458627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243444941181348916367278169 182583705886011687275458627)
      ·
        refine ⟨273875558829017530913187941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182583705886011687275458627 273875558829017530913187941)
        ·
          refine ⟨51351667280440787046222739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273875558829017530913187941 51351667280440787046222739)
          ·
            refine ⟨77027500920661180569334109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51351667280440787046222739 77027500920661180569334109)
            ·
              refine ⟨28885312845247942713500291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77027500920661180569334109 28885312845247942713500291)
              ·
                refine ⟨43327969267871914070250437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28885312845247942713500291 43327969267871914070250437)
                ·
                  refine ⟨8123994237725983888171957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43327969267871914070250437 8123994237725983888171957)
                  ·
                    refine ⟨761624459786810989516121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8123994237725983888171957 761624459786810989516121)
                    ·
                      rfl

theorem cell23_4449775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_4449775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449775 prefixEnd_4449775 := by exact prefixLift 4449775
  have htrace : WordTrace (prefixWord ++ tailWord_4449775) baseStart_4449775 baseEnd_4449775 := by
    simpa [prefixWord, tailWord_4449775, baseEnd_4449775] using wordTrace_append hprefix tailTrace_4449775
  have hstable : (prefixWord ++ tailWord_4449775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449775).length < 2 ^ (prefixWord ++ tailWord_4449775).sum := by decide
  have hdescent : baseEnd_4449775 < baseStart_4449775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449790 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4449790 : Nat := 118140960795 + 4449790 * 2 ^ 59
def prefixEnd_4449790 : Nat := 4983230072969 + 3 ^ 40 * 4449790 * 2
def baseEnd_4449790 : Nat := 2284881081570250409860795

theorem tailTrace_4449790 : CollatzResearch.WordTrace tailWord_4449790 prefixEnd_4449790 2284881081570250409860795 := by
  unfold tailWord_4449790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287146818647283559164353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108198116366118845648876549 20287146818647283559164353)
  ·
    refine ⟨15215360113985462669373265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20287146818647283559164353 15215360113985462669373265)
    ·
      refine ⟨11411520085489097002029949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15215360113985462669373265 11411520085489097002029949)
      ·
        refine ⟨4279320032058411375761231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11411520085489097002029949 4279320032058411375761231)
        ·
          refine ⟨6418980048087617063641847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279320032058411375761231 6418980048087617063641847)
          ·
            refine ⟨9628470072131425595462771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418980048087617063641847 9628470072131425595462771)
            ·
              refine ⟨14442705108197138393194157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9628470072131425595462771 14442705108197138393194157)
              ·
                refine ⟨5416014415573926897447809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14442705108197138393194157 5416014415573926897447809)
                ·
                  refine ⟨4062010811680445173085857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5416014415573926897447809 4062010811680445173085857)
                  ·
                    refine ⟨3046508108760333879814393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062010811680445173085857 3046508108760333879814393)
                    ·
                      refine ⟨2284881081570250409860795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046508108760333879814393 2284881081570250409860795)
                      ·
                        rfl

theorem cell23_4449790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4449790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449790 prefixEnd_4449790 := by exact prefixLift 4449790
  have htrace : WordTrace (prefixWord ++ tailWord_4449790) baseStart_4449790 baseEnd_4449790 := by
    simpa [prefixWord, tailWord_4449790, baseEnd_4449790] using wordTrace_append hprefix tailTrace_4449790
  have hstable : (prefixWord ++ tailWord_4449790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449790).length < 2 ^ (prefixWord ++ tailWord_4449790).sum := by decide
  have hdescent : baseEnd_4449790 < baseStart_4449790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449795 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_4449795 : Nat := 118140960795 + 4449795 * 2 ^ 59
def prefixEnd_4449795 : Nat := 4983230072969 + 3 ^ 40 * 4449795 * 2
def baseEnd_4449795 : Nat := 2284883648973522890298271

theorem tailTrace_4449795 : CollatzResearch.WordTrace tailWord_4449795 prefixEnd_4449795 2284883648973522890298271 := by
  unfold tailWord_4449795
  simp only [CollatzResearch.WordTrace]
  refine ⟨162297356914160154327246839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108198237942773436218164559 162297356914160154327246839)
  ·
    refine ⟨243446035371240231490870259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162297356914160154327246839 243446035371240231490870259)
    ·
      refine ⟨365169053056860347236305389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243446035371240231490870259 365169053056860347236305389)
      ·
        refine ⟨136938394896322630213614521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365169053056860347236305389 136938394896322630213614521)
        ·
          refine ⟨102703796172241972660210891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136938394896322630213614521 102703796172241972660210891)
          ·
            refine ⟨154055694258362958990316337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102703796172241972660210891 154055694258362958990316337)
            ·
              refine ⟨115541770693772219242737253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154055694258362958990316337 115541770693772219242737253)
              ·
                refine ⟨21664082005082291108013235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115541770693772219242737253 21664082005082291108013235)
                ·
                  refine ⟨32496123007623436662019853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21664082005082291108013235 32496123007623436662019853)
                  ·
                    refine ⟨12186046127858788748257445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32496123007623436662019853 12186046127858788748257445)
                    ·
                      refine ⟨2284883648973522890298271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12186046127858788748257445 2284883648973522890298271)
                      ·
                        rfl

theorem cell23_4449795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_4449795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449795 prefixEnd_4449795 := by exact prefixLift 4449795
  have htrace : WordTrace (prefixWord ++ tailWord_4449795) baseStart_4449795 baseEnd_4449795 := by
    simpa [prefixWord, tailWord_4449795, baseEnd_4449795] using wordTrace_append hprefix tailTrace_4449795
  have hstable : (prefixWord ++ tailWord_4449795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449795).length < 2 ^ (prefixWord ++ tailWord_4449795).sum := by decide
  have hdescent : baseEnd_4449795 < baseStart_4449795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449889 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_4449889 : Nat := 118140960795 + 4449889 * 2 ^ 59
def prefixEnd_4449889 : Nat := 4983230072969 + 3 ^ 40 * 4449889 * 2
def baseEnd_4449889 : Nat := 2284931916155045522522839

theorem tailTrace_4449889 : CollatzResearch.WordTrace tailWord_4449889 prefixEnd_4449889 2284931916155045522522839 := by
  unfold tailWord_4449889
  simp only [CollatzResearch.WordTrace]
  refine ⟨162300785375819608381168721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108200523583879738920779147 162300785375819608381168721)
  ·
    refine ⟨121725589031864706285876541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162300785375819608381168721 121725589031864706285876541)
    ·
      refine ⟨45647095886949264857203703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121725589031864706285876541 45647095886949264857203703)
      ·
        refine ⟨68470643830423897285805555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45647095886949264857203703 68470643830423897285805555)
        ·
          refine ⟨102705965745635845928708333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68470643830423897285805555 102705965745635845928708333)
          ·
            refine ⟨38514737154613442223265625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102705965745635845928708333 38514737154613442223265625)
            ·
              refine ⟨28886052865960081667449219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38514737154613442223265625 28886052865960081667449219)
              ·
                refine ⟨43329079298940122501173829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28886052865960081667449219 43329079298940122501173829)
                ·
                  refine ⟨8124202368551272968970093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43329079298940122501173829 8124202368551272968970093)
                  ·
                    refine ⟨3046575888206727363363785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8124202368551272968970093 3046575888206727363363785)
                    ·
                      refine ⟨2284931916155045522522839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046575888206727363363785 2284931916155045522522839)
                      ·
                        rfl

theorem cell23_4449889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_4449889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449889 prefixEnd_4449889 := by exact prefixLift 4449889
  have htrace : WordTrace (prefixWord ++ tailWord_4449889) baseStart_4449889 baseEnd_4449889 := by
    simpa [prefixWord, tailWord_4449889, baseEnd_4449889] using wordTrace_append hprefix tailTrace_4449889
  have hstable : (prefixWord ++ tailWord_4449889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449889).length < 2 ^ (prefixWord ++ tailWord_4449889).sum := by decide
  have hdescent : baseEnd_4449889 < baseStart_4449889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449896 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4449896 : Nat := 118140960795 + 4449896 * 2 ^ 59
def prefixEnd_4449896 : Nat := 4983230072969 + 3 ^ 40 * 4449896 * 2
def baseEnd_4449896 : Nat := 2284935510519626995135307

theorem tailTrace_4449896 : CollatzResearch.WordTrace tailWord_4449896 prefixEnd_4449896 2284935510519626995135307 := by
  unfold tailWord_4449896
  simp only [CollatzResearch.WordTrace]
  refine ⟨81150520343397124288336771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108200693791196165717782361 81150520343397124288336771)
  ·
    refine ⟨121725780515095686432505157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81150520343397124288336771 121725780515095686432505157)
    ·
      refine ⟨22823583846580441206094717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121725780515095686432505157 22823583846580441206094717)
      ·
        refine ⟨8558843942467665452285519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22823583846580441206094717 8558843942467665452285519)
        ·
          refine ⟨12838265913701498178428279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558843942467665452285519 12838265913701498178428279)
          ·
            refine ⟨19257398870552247267642419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12838265913701498178428279 19257398870552247267642419)
            ·
              refine ⟨28886098305828370901463629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19257398870552247267642419 28886098305828370901463629)
              ·
                refine ⟨10832286864685639088048861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28886098305828370901463629 10832286864685639088048861)
                ·
                  refine ⟨4062107574257114658018323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10832286864685639088048861 4062107574257114658018323)
                  ·
                    refine ⟨6093161361385671987027485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062107574257114658018323 6093161361385671987027485)
                    ·
                      refine ⟨2284935510519626995135307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093161361385671987027485 2284935510519626995135307)
                      ·
                        rfl

theorem cell23_4449896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4449896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449896 prefixEnd_4449896 := by exact prefixLift 4449896
  have htrace : WordTrace (prefixWord ++ tailWord_4449896) baseStart_4449896 baseEnd_4449896 := by
    simpa [prefixWord, tailWord_4449896, baseEnd_4449896] using wordTrace_append hprefix tailTrace_4449896
  have hstable : (prefixWord ++ tailWord_4449896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449896).length < 2 ^ (prefixWord ++ tailWord_4449896).sum := by decide
  have hdescent : baseEnd_4449896 < baseStart_4449896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449912 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_4449912 : Nat := 118140960795 + 4449912 * 2 ^ 59
def prefixEnd_4449912 : Nat := 4983230072969 + 3 ^ 40 * 4449912 * 2
def baseEnd_4449912 : Nat := 761647908736699644178411

theorem tailTrace_4449912 : CollatzResearch.WordTrace tailWord_4449912 prefixEnd_4449912 761647908736699644178411 := by
  unfold tailWord_4449912
  simp only [CollatzResearch.WordTrace]
  refine ⟨81150812127368141654627995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108201082836490855539503993 81150812127368141654627995)
  ·
    refine ⟨121726218191052212481941993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81150812127368141654627995 121726218191052212481941993)
    ·
      refine ⟨91294663643289159361456495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121726218191052212481941993 91294663643289159361456495)
      ·
        refine ⟨136941995464933739042184743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91294663643289159361456495 136941995464933739042184743)
        ·
          refine ⟨205412993197400608563277115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136941995464933739042184743 205412993197400608563277115)
          ·
            refine ⟨308119489796100912844915673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205412993197400608563277115 308119489796100912844915673)
            ·
              refine ⟨231089617347075684633686755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308119489796100912844915673 231089617347075684633686755)
              ·
                refine ⟨346634426020613526950530133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231089617347075684633686755 346634426020613526950530133)
                ·
                  refine ⟨4062122179929064768951525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 346634426020613526950530133 4062122179929064768951525)
                  ·
                    refine ⟨761647908736699644178411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4062122179929064768951525 761647908736699644178411)
                    ·
                      rfl

theorem cell23_4449912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_4449912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449912 prefixEnd_4449912 := by exact prefixLift 4449912
  have htrace : WordTrace (prefixWord ++ tailWord_4449912) baseStart_4449912 baseEnd_4449912 := by
    simpa [prefixWord, tailWord_4449912, baseEnd_4449912] using wordTrace_append hprefix tailTrace_4449912
  have hstable : (prefixWord ++ tailWord_4449912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449912).length < 2 ^ (prefixWord ++ tailWord_4449912).sum := by decide
  have hdescent : baseEnd_4449912 < baseStart_4449912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449930 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_4449930 : Nat := 118140960795 + 4449930 * 2 ^ 59
def prefixEnd_4449930 : Nat := 4983230072969 + 3 ^ 40 * 4449930 * 2
def baseEnd_4449930 : Nat := 2284952968861879862110151

theorem tailTrace_4449930 : CollatzResearch.WordTrace tailWord_4449930 prefixEnd_4449930 2284952968861879862110151 := by
  unfold tailWord_4449930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40575570192167768095852811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108201520512447381588940829 40575570192167768095852811)
  ·
    refine ⟨60863355288251652143779217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40575570192167768095852811 60863355288251652143779217)
    ·
      refine ⟨45647516466188739107834413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60863355288251652143779217 45647516466188739107834413)
      ·
        refine ⟨17117818674820777165437905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45647516466188739107834413 17117818674820777165437905)
        ·
          refine ⟨12838364006115582874078429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17117818674820777165437905 12838364006115582874078429)
          ·
            refine ⟨4814386502293343577779411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12838364006115582874078429 4814386502293343577779411)
            ·
              refine ⟨7221579753440015366669117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814386502293343577779411 7221579753440015366669117)
              ·
                refine ⟨2708092407540005762500919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7221579753440015366669117 2708092407540005762500919)
                ·
                  refine ⟨4062138611310008643751379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708092407540005762500919 4062138611310008643751379)
                  ·
                    refine ⟨6093207916965012965627069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062138611310008643751379 6093207916965012965627069)
                    ·
                      refine ⟨2284952968861879862110151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093207916965012965627069 2284952968861879862110151)
                      ·
                        rfl

theorem cell23_4449930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_4449930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449930 prefixEnd_4449930 := by exact prefixLift 4449930
  have htrace : WordTrace (prefixWord ++ tailWord_4449930) baseStart_4449930 baseEnd_4449930 := by
    simpa [prefixWord, tailWord_4449930, baseEnd_4449930] using wordTrace_append hprefix tailTrace_4449930
  have hstable : (prefixWord ++ tailWord_4449930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449930).length < 2 ^ (prefixWord ++ tailWord_4449930).sum := by decide
  have hdescent : baseEnd_4449930 < baseStart_4449930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449932 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4449932 : Nat := 118140960795 + 4449932 * 2 ^ 59
def prefixEnd_4449932 : Nat := 4983230072969 + 3 ^ 40 * 4449932 * 2
def baseEnd_4449932 : Nat := 2284953995823188854285141

theorem tailTrace_4449932 : CollatzResearch.WordTrace tailWord_4449932 prefixEnd_4449932 2284953995823188854285141 := by
  unfold tailWord_4449932
  simp only [CollatzResearch.WordTrace]
  refine ⟨81151176857331913362492025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108201569143109217816656033 81151176857331913362492025)
  ·
    refine ⟨60863382642998935021869019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81151176857331913362492025 60863382642998935021869019)
    ·
      refine ⟨91295073964498402532803529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60863382642998935021869019 91295073964498402532803529)
      ·
        refine ⟨68471305473373801899602647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91295073964498402532803529 68471305473373801899602647)
        ·
          refine ⟨102706958210060702849403971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68471305473373801899602647 102706958210060702849403971)
          ·
            refine ⟨154060437315091054274105957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102706958210060702849403971 154060437315091054274105957)
            ·
              refine ⟨28886331996579572676394867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154060437315091054274105957 28886331996579572676394867)
              ·
                refine ⟨43329497994869359014592301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28886331996579572676394867 43329497994869359014592301)
                ·
                  refine ⟨16248561748076009630472113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43329497994869359014592301 16248561748076009630472113)
                  ·
                    refine ⟨12186421311057007222854085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16248561748076009630472113 12186421311057007222854085)
                    ·
                      refine ⟨2284953995823188854285141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12186421311057007222854085 2284953995823188854285141)
                      ·
                        rfl

theorem cell23_4449932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4449932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449932 prefixEnd_4449932 := by exact prefixLift 4449932
  have htrace : WordTrace (prefixWord ++ tailWord_4449932) baseStart_4449932 baseEnd_4449932 := by
    simpa [prefixWord, tailWord_4449932, baseEnd_4449932] using wordTrace_append hprefix tailTrace_4449932
  have hstable : (prefixWord ++ tailWord_4449932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449932).length < 2 ^ (prefixWord ++ tailWord_4449932).sum := by decide
  have hdescent : baseEnd_4449932 < baseStart_4449932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449953 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4449953 : Nat := 118140960795 + 4449953 * 2 ^ 59
def prefixEnd_4449953 : Nat := 4983230072969 + 3 ^ 40 * 4449953 * 2
def baseEnd_4449953 : Nat := 2284964778916933272122545

theorem tailTrace_4449953 : CollatzResearch.WordTrace tailWord_4449953 prefixEnd_4449953 2284964778916933272122545 := by
  unfold tailWord_4449953
  simp only [CollatzResearch.WordTrace]
  refine ⟨162303119647587747311498513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108202079765058498207665675 162303119647587747311498513)
  ·
    refine ⟨121727339735690810483623885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162303119647587747311498513 121727339735690810483623885)
    ·
      refine ⟨45647752400884053931358957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121727339735690810483623885 45647752400884053931358957)
      ·
        refine ⟨17117907150331520224259609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45647752400884053931358957 17117907150331520224259609)
        ·
          refine ⟨12838430362748640168194707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17117907150331520224259609 12838430362748640168194707)
          ·
            refine ⟨19257645544122960252292061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12838430362748640168194707 19257645544122960252292061)
            ·
              refine ⟨7221617079046110094609523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19257645544122960252292061 7221617079046110094609523)
              ·
                refine ⟨10832425618569165141914285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221617079046110094609523 10832425618569165141914285)
                ·
                  refine ⟨4062159606963436928217857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10832425618569165141914285 4062159606963436928217857)
                  ·
                    refine ⟨3046619705222577696163393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062159606963436928217857 3046619705222577696163393)
                    ·
                      refine ⟨2284964778916933272122545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046619705222577696163393 2284964778916933272122545)
                      ·
                        rfl

theorem cell23_4449953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4449953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449953 prefixEnd_4449953 := by exact prefixLift 4449953
  have htrace : WordTrace (prefixWord ++ tailWord_4449953) baseStart_4449953 baseEnd_4449953 := by
    simpa [prefixWord, tailWord_4449953, baseEnd_4449953] using wordTrace_append hprefix tailTrace_4449953
  have hstable : (prefixWord ++ tailWord_4449953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449953).length < 2 ^ (prefixWord ++ tailWord_4449953).sum := by decide
  have hdescent : baseEnd_4449953 < baseStart_4449953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4449990 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4449990 : Nat := 118140960795 + 4449990 * 2 ^ 59
def prefixEnd_4449990 : Nat := 4983230072969 + 3 ^ 40 * 4449990 * 2
def baseEnd_4449990 : Nat := 2284983777701149627359875

theorem tailTrace_4449990 : CollatzResearch.WordTrace tailWord_4449990 prefixEnd_4449990 2284983777701149627359875 := by
  unfold tailWord_4449990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5072014660889178207206107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108202979432302468420396949 5072014660889178207206107)
  ·
    refine ⟨7608021991333767310809161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5072014660889178207206107 7608021991333767310809161)
    ·
      refine ⟨5706016493500325483106871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7608021991333767310809161 5706016493500325483106871)
      ·
        refine ⟨8559024740250488224660307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706016493500325483106871 8559024740250488224660307)
        ·
          refine ⟨12838537110375732336990461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559024740250488224660307 12838537110375732336990461)
          ·
            refine ⟨4814451416390899626371423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12838537110375732336990461 4814451416390899626371423)
            ·
              refine ⟨7221677124586349439557135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814451416390899626371423 7221677124586349439557135)
              ·
                refine ⟨10832515686879524159335703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221677124586349439557135 10832515686879524159335703)
                ·
                  refine ⟨16248773530319286239003555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10832515686879524159335703 16248773530319286239003555)
                  ·
                    refine ⟨24373160295478929358505333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16248773530319286239003555 24373160295478929358505333)
                    ·
                      refine ⟨2284983777701149627359875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24373160295478929358505333 2284983777701149627359875)
                      ·
                        rfl

theorem cell23_4449990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4449990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4449990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4449990 prefixEnd_4449990 := by exact prefixLift 4449990
  have htrace : WordTrace (prefixWord ++ tailWord_4449990) baseStart_4449990 baseEnd_4449990 := by
    simpa [prefixWord, tailWord_4449990, baseEnd_4449990] using wordTrace_append hprefix tailTrace_4449990
  have hstable : (prefixWord ++ tailWord_4449990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4449990).length < 2 ^ (prefixWord ++ tailWord_4449990).sum := by decide
  have hdescent : baseEnd_4449990 < baseStart_4449990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4449990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450004 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4450004 : Nat := 118140960795 + 4450004 * 2 ^ 59
def prefixEnd_4450004 : Nat := 4983230072969 + 3 ^ 40 * 4450004 * 2
def baseEnd_4450004 : Nat := 2284990966430312572584811

theorem tailTrace_4450004 : CollatzResearch.WordTrace tailWord_4450004 prefixEnd_4450004 2284990966430312572584811 := by
  unfold tailWord_4450004
  simp only [CollatzResearch.WordTrace]
  refine ⟨81152489885201491510802533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108203319846935322014403377 81152489885201491510802533)
  ·
    refine ⟨15216091853475279658275475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81152489885201491510802533 15216091853475279658275475)
    ·
      refine ⟨22824137780212919487413213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15216091853475279658275475 22824137780212919487413213)
      ·
        refine ⟨8559051667579844807779955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22824137780212919487413213 8559051667579844807779955)
        ·
          refine ⟨12838577501369767211669933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559051667579844807779955 12838577501369767211669933)
          ·
            refine ⟨4814466563013662704376225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12838577501369767211669933 4814466563013662704376225)
            ·
              refine ⟨3610849922260247028282169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814466563013662704376225 3610849922260247028282169)
              ·
                refine ⟨2708137441695185271211627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610849922260247028282169 2708137441695185271211627)
                ·
                  refine ⟨4062206162542777906817441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708137441695185271211627 4062206162542777906817441)
                  ·
                    refine ⟨3046654621907083430113081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062206162542777906817441 3046654621907083430113081)
                    ·
                      refine ⟨2284990966430312572584811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046654621907083430113081 2284990966430312572584811)
                      ·
                        rfl

theorem cell23_4450004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4450004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450004 prefixEnd_4450004 := by exact prefixLift 4450004
  have htrace : WordTrace (prefixWord ++ tailWord_4450004) baseStart_4450004 baseEnd_4450004 := by
    simpa [prefixWord, tailWord_4450004, baseEnd_4450004] using wordTrace_append hprefix tailTrace_4450004
  have hstable : (prefixWord ++ tailWord_4450004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450004).length < 2 ^ (prefixWord ++ tailWord_4450004).sum := by decide
  have hdescent : baseEnd_4450004 < baseStart_4450004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450026 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_4450026 : Nat := 118140960795 + 4450026 * 2 ^ 59
def prefixEnd_4450026 : Nat := 4983230072969 + 3 ^ 40 * 4450026 * 2
def baseEnd_4450026 : Nat := 2285002263004711486509709

theorem tailTrace_4450026 : CollatzResearch.WordTrace tailWord_4450026 prefixEnd_4450026 2285002263004711486509709 := by
  unfold tailWord_4450026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40576445544080820194726483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108203854784215520519270621 40576445544080820194726483)
  ·
    refine ⟨60864668316121230292089725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40576445544080820194726483 60864668316121230292089725)
    ·
      refine ⟨22824250618545461359533647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60864668316121230292089725 22824250618545461359533647)
      ·
        refine ⟨34236375927818192039300471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22824250618545461359533647 34236375927818192039300471)
        ·
          refine ⟨51354563891727288058950707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34236375927818192039300471 51354563891727288058950707)
          ·
            refine ⟨77031845837590932088426061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51354563891727288058950707 77031845837590932088426061)
            ·
              refine ⟨28886942189096599533159773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77031845837590932088426061 28886942189096599533159773)
              ·
                refine ⟨10832603320911224824934915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28886942189096599533159773 10832603320911224824934915)
                ·
                  refine ⟨16248904981366837237402373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10832603320911224824934915 16248904981366837237402373)
                  ·
                    refine ⟨3046669684006281982012945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16248904981366837237402373 3046669684006281982012945)
                    ·
                      refine ⟨2285002263004711486509709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046669684006281982012945 2285002263004711486509709)
                      ·
                        rfl

theorem cell23_4450026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_4450026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450026 prefixEnd_4450026 := by exact prefixLift 4450026
  have htrace : WordTrace (prefixWord ++ tailWord_4450026) baseStart_4450026 baseEnd_4450026 := by
    simpa [prefixWord, tailWord_4450026, baseEnd_4450026] using wordTrace_append hprefix tailTrace_4450026
  have hstable : (prefixWord ++ tailWord_4450026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450026).length < 2 ^ (prefixWord ++ tailWord_4450026).sum := by decide
  have hdescent : baseEnd_4450026 < baseStart_4450026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_4450042 : Nat := 118140960795 + 4450042 * 2 ^ 59
def prefixEnd_4450042 : Nat := 4983230072969 + 3 ^ 40 * 4450042 * 2
def baseEnd_4450042 : Nat := 2285010478695183423909635

theorem tailTrace_4450042 : CollatzResearch.WordTrace tailWord_4450042 prefixEnd_4450042 2285010478695183423909635 := by
  unfold tailWord_4450042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40576591436066328877872095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108204243829510210340992253 40576591436066328877872095)
  ·
    refine ⟨60864887154099493316808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40576591436066328877872095 60864887154099493316808143)
    ·
      refine ⟨91297330731149239975212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60864887154099493316808143 91297330731149239975212215)
      ·
        refine ⟨136945996096723859962818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91297330731149239975212215 136945996096723859962818323)
        ·
          refine ⟨205418994145085789944227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136945996096723859962818323 205418994145085789944227485)
          ·
            refine ⟨77032122804407171229085307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205418994145085789944227485 77032122804407171229085307)
            ·
              refine ⟨115548184206610756843627961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77032122804407171229085307 115548184206610756843627961)
              ·
                refine ⟨86661138154958067632720971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115548184206610756843627961 86661138154958067632720971)
                ·
                  refine ⟨129991707232437101449081457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86661138154958067632720971 129991707232437101449081457)
                  ·
                    refine ⟨97493780424327826086811093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129991707232437101449081457 97493780424327826086811093)
                    ·
                      refine ⟨2285010478695183423909635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97493780424327826086811093 2285010478695183423909635)
                      ·
                        rfl

theorem cell23_4450042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_4450042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450042 prefixEnd_4450042 := by exact prefixLift 4450042
  have htrace : WordTrace (prefixWord ++ tailWord_4450042) baseStart_4450042 baseEnd_4450042 := by
    simpa [prefixWord, tailWord_4450042, baseEnd_4450042] using wordTrace_append hprefix tailTrace_4450042
  have hstable : (prefixWord ++ tailWord_4450042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450042).length < 2 ^ (prefixWord ++ tailWord_4450042).sum := by decide
  have hdescent : baseEnd_4450042 < baseStart_4450042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450059 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3]
def baseStart_4450059 : Nat := 118140960795 + 4450059 * 2 ^ 59
def prefixEnd_4450059 : Nat := 4983230072969 + 3 ^ 40 * 4450059 * 2
def baseEnd_4450059 : Nat := 2285019207866309857397057

theorem tailTrace_4450059 : CollatzResearch.WordTrace tailWord_4450059 prefixEnd_4450059 2285019207866309857397057 := by
  unfold tailWord_4450059
  simp only [CollatzResearch.WordTrace]
  refine ⟨162306985785203727414857231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108204657190135818276571487 162306985785203727414857231)
  ·
    refine ⟨243460478677805591122285847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162306985785203727414857231 243460478677805591122285847)
    ·
      refine ⟨365190718016708386683428771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243460478677805591122285847 365190718016708386683428771)
      ·
        refine ⟨547786077025062580025143157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365190718016708386683428771 547786077025062580025143157)
        ·
          refine ⟨51354944721099616877357171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 547786077025062580025143157 51354944721099616877357171)
          ·
            refine ⟨77032417081649425316035757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51354944721099616877357171 77032417081649425316035757)
            ·
              refine ⟨28887156405618534493513409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77032417081649425316035757 28887156405618534493513409)
              ·
                refine ⟨21665367304213900870135057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28887156405618534493513409 21665367304213900870135057)
                ·
                  refine ⟨16249025478160425652601293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21665367304213900870135057 16249025478160425652601293)
                  ·
                    refine ⟨6093384554310159619725485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16249025478160425652601293 6093384554310159619725485)
                    ·
                      refine ⟨2285019207866309857397057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093384554310159619725485 2285019207866309857397057)
                      ·
                        rfl

theorem cell23_4450059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].length) (baseStart_4450059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450059 prefixEnd_4450059 := by exact prefixLift 4450059
  have htrace : WordTrace (prefixWord ++ tailWord_4450059) baseStart_4450059 baseEnd_4450059 := by
    simpa [prefixWord, tailWord_4450059, baseEnd_4450059] using wordTrace_append hprefix tailTrace_4450059
  have hstable : (prefixWord ++ tailWord_4450059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450059).length < 2 ^ (prefixWord ++ tailWord_4450059).sum := by decide
  have hdescent : baseEnd_4450059 < baseStart_4450059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450066 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_4450066 : Nat := 118140960795 + 4450066 * 2 ^ 59
def prefixEnd_4450066 : Nat := 4983230072969 + 3 ^ 40 * 4450066 * 2
def baseEnd_4450066 : Nat := 253891422470099036667725

theorem tailTrace_4450066 : CollatzResearch.WordTrace tailWord_4450066 prefixEnd_4450066 253891422470099036667725 := by
  unfold tailWord_4450066
  simp only [CollatzResearch.WordTrace]
  refine ⟨40576810274044591902590513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108204827397452245073574701 40576810274044591902590513)
  ·
    refine ⟨30432607705533443926942885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40576810274044591902590513 30432607705533443926942885)
    ·
      refine ⟨5706113944787520736301791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30432607705533443926942885 5706113944787520736301791)
      ·
        refine ⟨8559170917181281104452687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706113944787520736301791 8559170917181281104452687)
        ·
          refine ⟨12838756375771921656679031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559170917181281104452687 12838756375771921656679031)
          ·
            refine ⟨19258134563657882485018547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12838756375771921656679031 19258134563657882485018547)
            ·
              refine ⟨28887201845486823727527821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19258134563657882485018547 28887201845486823727527821)
              ·
                refine ⟨10832700692057558897822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28887201845486823727527821 10832700692057558897822933)
                ·
                  refine ⟨253891422470099036667725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10832700692057558897822933 253891422470099036667725)
                  ·
                    rfl

theorem cell23_4450066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_4450066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450066 prefixEnd_4450066 := by exact prefixLift 4450066
  have htrace : WordTrace (prefixWord ++ tailWord_4450066) baseStart_4450066 baseEnd_4450066 := by
    simpa [prefixWord, tailWord_4450066, baseEnd_4450066] using wordTrace_append hprefix tailTrace_4450066
  have hstable : (prefixWord ++ tailWord_4450066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450066).length < 2 ^ (prefixWord ++ tailWord_4450066).sum := by decide
  have hdescent : baseEnd_4450066 < baseStart_4450066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450100 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4450100 : Nat := 118140960795 + 4450100 * 2 ^ 59
def prefixEnd_4450100 : Nat := 4983230072969 + 3 ^ 40 * 4450100 * 2
def baseEnd_4450100 : Nat := 253893362285904910776041

theorem tailTrace_4450100 : CollatzResearch.WordTrace tailWord_4450100 prefixEnd_4450100 253893362285904910776041 := by
  unfold tailWord_4450100
  simp only [CollatzResearch.WordTrace]
  refine ⟨81154240589027595708549877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108205654118703460944733169 81154240589027595708549877)
  ·
    refine ⟨7608210055221337097676551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81154240589027595708549877 7608210055221337097676551)
    ·
      refine ⟨11412315082832005646514827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7608210055221337097676551 11412315082832005646514827)
      ·
        refine ⟨17118472624248008469772241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11412315082832005646514827 17118472624248008469772241)
        ·
          refine ⟨12838854468186006352329181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17118472624248008469772241 12838854468186006352329181)
          ·
            refine ⟨4814570425569752382123443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12838854468186006352329181 4814570425569752382123443)
            ·
              refine ⟨7221855638354628573185165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814570425569752382123443 7221855638354628573185165)
              ·
                refine ⟨2708195864382985714944437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7221855638354628573185165 2708195864382985714944437)
                ·
                  refine ⟨253893362285904910776041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708195864382985714944437 253893362285904910776041)
                  ·
                    rfl

theorem cell23_4450100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4450100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450100 prefixEnd_4450100 := by exact prefixLift 4450100
  have htrace : WordTrace (prefixWord ++ tailWord_4450100) baseStart_4450100 baseEnd_4450100 := by
    simpa [prefixWord, tailWord_4450100, baseEnd_4450100] using wordTrace_append hprefix tailTrace_4450100
  have hstable : (prefixWord ++ tailWord_4450100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450100).length < 2 ^ (prefixWord ++ tailWord_4450100).sum := by decide
  have hdescent : baseEnd_4450100 < baseStart_4450100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450177 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4450177 : Nat := 118140960795 + 4450177 * 2 ^ 59
def prefixEnd_4450177 : Nat := 4983230072969 + 3 ^ 40 * 4450177 * 2
def baseEnd_4450177 : Nat := 761693266194513465240505

theorem tailTrace_4450177 : CollatzResearch.WordTrace tailWord_4450177 prefixEnd_4450177 761693266194513465240505 := by
  unfold tailWord_4450177
  simp only [CollatzResearch.WordTrace]
  refine ⟨162311289598776233567652785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108207526399184155711768523 162311289598776233567652785)
  ·
    refine ⟨121733467199082175175739589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162311289598776233567652785 121733467199082175175739589)
    ·
      refine ⟨22825025099827907845451173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121733467199082175175739589 22825025099827907845451173)
      ·
        refine ⟨4279692206217732721022095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22825025099827907845451173 4279692206217732721022095)
        ·
          refine ⟨6419538309326599081533143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279692206217732721022095 6419538309326599081533143)
          ·
            refine ⟨9629307463989898622299715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419538309326599081533143 9629307463989898622299715)
            ·
              refine ⟨14443961195984847933449573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9629307463989898622299715 14443961195984847933449573)
              ·
                refine ⟨2708242724247158987521795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14443961195984847933449573 2708242724247158987521795)
                ·
                  refine ⟨4062364086370738481282693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708242724247158987521795 4062364086370738481282693)
                  ·
                    refine ⟨761693266194513465240505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4062364086370738481282693 761693266194513465240505)
                    ·
                      rfl

theorem cell23_4450177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4450177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450177 prefixEnd_4450177 := by exact prefixLift 4450177
  have htrace : WordTrace (prefixWord ++ tailWord_4450177) baseStart_4450177 baseEnd_4450177 := by
    simpa [prefixWord, tailWord_4450177, baseEnd_4450177] using wordTrace_append hprefix tailTrace_4450177
  have hstable : (prefixWord ++ tailWord_4450177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450177).length < 2 ^ (prefixWord ++ tailWord_4450177).sum := by decide
  have hdescent : baseEnd_4450177 < baseStart_4450177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450210 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_4450210 : Nat := 118140960795 + 4450210 * 2 ^ 59
def prefixEnd_4450210 : Nat := 4983230072969 + 3 ^ 40 * 4450210 * 2
def baseEnd_4450210 : Nat := 2285096743445138766608863

theorem tailTrace_4450210 : CollatzResearch.WordTrace tailWord_4450210 prefixEnd_4450210 2285096743445138766608863 := by
  unfold tailWord_4450210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40578123301914170050901021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108208328805104453469069389 40578123301914170050901021)
  ·
    refine ⟨15216796238217813769087883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40578123301914170050901021 15216796238217813769087883)
    ·
      refine ⟨22825194357326720653631825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15216796238217813769087883 22825194357326720653631825)
      ·
        refine ⟨17118895767995040490223869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22825194357326720653631825 17118895767995040490223869)
        ·
          refine ⟨6419585912998140183833951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17118895767995040490223869 6419585912998140183833951)
          ·
            refine ⟨9629378869497210275750927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419585912998140183833951 9629378869497210275750927)
            ·
              refine ⟨14444068304245815413626391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9629378869497210275750927 14444068304245815413626391)
              ·
                refine ⟨21666102456368723120439587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14444068304245815413626391 21666102456368723120439587)
                ·
                  refine ⟨32499153684553084680659381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21666102456368723120439587 32499153684553084680659381)
                  ·
                    refine ⟨3046795657926851688811817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32499153684553084680659381 3046795657926851688811817)
                    ·
                      refine ⟨2285096743445138766608863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046795657926851688811817 2285096743445138766608863)
                      ·
                        rfl

theorem cell23_4450210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_4450210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450210 prefixEnd_4450210 := by exact prefixLift 4450210
  have htrace : WordTrace (prefixWord ++ tailWord_4450210) baseStart_4450210 baseEnd_4450210 := by
    simpa [prefixWord, tailWord_4450210, baseEnd_4450210] using wordTrace_append hprefix tailTrace_4450210
  have hstable : (prefixWord ++ tailWord_4450210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450210).length < 2 ^ (prefixWord ++ tailWord_4450210).sum := by decide
  have hdescent : baseEnd_4450210 < baseStart_4450210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450223 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 5, 2, 2]
def baseStart_4450223 : Nat := 118140960795 + 4450223 * 2 ^ 59
def prefixEnd_4450223 : Nat := 4983230072969 + 3 ^ 40 * 4450223 * 2
def baseEnd_4450223 : Nat := 2285103418693647215746303

theorem tailTrace_4450223 : CollatzResearch.WordTrace tailWord_4450223 prefixEnd_4450223 2285103418693647215746303 := by
  unfold tailWord_4450223
  simp only [CollatzResearch.WordTrace]
  refine ⟨162312967356609583423827323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108208644904406388949218215 162312967356609583423827323)
  ·
    refine ⟨243469451034914375135740985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162312967356609583423827323 243469451034914375135740985)
    ·
      refine ⟨182602088276185781351805739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243469451034914375135740985 182602088276185781351805739)
      ·
        refine ⟨273903132414278672027708609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182602088276185781351805739 273903132414278672027708609)
        ·
          refine ⟨205427349310709004020781457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273903132414278672027708609 205427349310709004020781457)
          ·
            refine ⟨154070511983031753015586093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205427349310709004020781457 154070511983031753015586093)
            ·
              refine ⟨57776441993636907380844785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154070511983031753015586093 57776441993636907380844785)
              ·
                refine ⟨43332331495227680535633589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57776441993636907380844785 43332331495227680535633589)
                ·
                  refine ⟨4062406077677595050215649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43332331495227680535633589 4062406077677595050215649)
                  ·
                    refine ⟨3046804558258196287661737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062406077677595050215649 3046804558258196287661737)
                    ·
                      refine ⟨2285103418693647215746303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046804558258196287661737 2285103418693647215746303)
                      ·
                        rfl

theorem cell23_4450223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2, 2].length) (baseStart_4450223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450223 prefixEnd_4450223 := by exact prefixLift 4450223
  have htrace : WordTrace (prefixWord ++ tailWord_4450223) baseStart_4450223 baseEnd_4450223 := by
    simpa [prefixWord, tailWord_4450223, baseEnd_4450223] using wordTrace_append hprefix tailTrace_4450223
  have hstable : (prefixWord ++ tailWord_4450223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450223).length < 2 ^ (prefixWord ++ tailWord_4450223).sum := by decide
  have hdescent : baseEnd_4450223 < baseStart_4450223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450240 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2]
def baseStart_4450240 : Nat := 118140960795 + 4450240 * 2 ^ 59
def prefixEnd_4450240 : Nat := 4983230072969 + 3 ^ 40 * 4450240 * 2
def baseEnd_4450240 : Nat := 2285112147864773649233725

theorem tailTrace_4450240 : CollatzResearch.WordTrace tailWord_4450240 prefixEnd_4450240 2285112147864773649233725 := by
  unfold tailWord_4450240
  simp only [CollatzResearch.WordTrace]
  refine ⟨81156793698773997663598087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108209058265031996884797449 81156793698773997663598087)
  ·
    refine ⟨121735190548160996495397131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81156793698773997663598087 121735190548160996495397131)
    ·
      refine ⟨182602785822241494743095697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121735190548160996495397131 182602785822241494743095697)
      ·
        refine ⟨136952089366681121057321773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182602785822241494743095697 136952089366681121057321773)
        ·
          refine ⟨51357033512505420396495665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136952089366681121057321773 51357033512505420396495665)
          ·
            refine ⟨38517775134379065297371749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51357033512505420396495665 38517775134379065297371749)
            ·
              refine ⟨7222082837696074743257203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38517775134379065297371749 7222082837696074743257203)
              ·
                refine ⟨10833124256544112114885805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222082837696074743257203 10833124256544112114885805)
                ·
                  refine ⟨4062421596204042043082177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10833124256544112114885805 4062421596204042043082177)
                  ·
                    refine ⟨3046816197153031532311633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062421596204042043082177 3046816197153031532311633)
                    ·
                      refine ⟨2285112147864773649233725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046816197153031532311633 2285112147864773649233725)
                      ·
                        rfl

theorem cell23_4450240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_4450240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450240 prefixEnd_4450240 := by exact prefixLift 4450240
  have htrace : WordTrace (prefixWord ++ tailWord_4450240) baseStart_4450240 baseEnd_4450240 := by
    simpa [prefixWord, tailWord_4450240, baseEnd_4450240] using wordTrace_append hprefix tailTrace_4450240
  have hstable : (prefixWord ++ tailWord_4450240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450240).length < 2 ^ (prefixWord ++ tailWord_4450240).sum := by decide
  have hdescent : baseEnd_4450240 < baseStart_4450240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450249 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_4450249 : Nat := 118140960795 + 4450249 * 2 ^ 59
def prefixEnd_4450249 : Nat := 4983230072969 + 3 ^ 40 * 4450249 * 2
def baseEnd_4450249 : Nat := 2285116769190664114021183

theorem tailTrace_4450249 : CollatzResearch.WordTrace tailWord_4450249 prefixEnd_4450249 2285116769190664114021183 := by
  unfold tailWord_4450249
  simp only [CollatzResearch.WordTrace]
  refine ⟨162313915654515389864273801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108209277103010259909515867 162313915654515389864273801)
  ·
    refine ⟨121735436740886542398205351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162313915654515389864273801 121735436740886542398205351)
    ·
      refine ⟨182603155111329813597308027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121735436740886542398205351 182603155111329813597308027)
      ·
        refine ⟨273904732666994720395962041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182603155111329813597308027 273904732666994720395962041)
        ·
          refine ⟨205428549500246040296971531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273904732666994720395962041 205428549500246040296971531)
          ·
            refine ⟨308142824250369060445457297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205428549500246040296971531 308142824250369060445457297)
            ·
              refine ⟨231107118187776795334092973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308142824250369060445457297 231107118187776795334092973)
              ·
                refine ⟨86665169320416298250284865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231107118187776795334092973 86665169320416298250284865)
                ·
                  refine ⟨64998876990312223687713649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86665169320416298250284865 64998876990312223687713649)
                  ·
                    refine ⟨48749157742734167765785237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64998876990312223687713649 48749157742734167765785237)
                    ·
                      refine ⟨2285116769190664114021183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48749157742734167765785237 2285116769190664114021183)
                      ·
                        rfl

theorem cell23_4450249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_4450249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450249 prefixEnd_4450249 := by exact prefixLift 4450249
  have htrace : WordTrace (prefixWord ++ tailWord_4450249) baseStart_4450249 baseEnd_4450249 := by
    simpa [prefixWord, tailWord_4450249, baseEnd_4450249] using wordTrace_append hprefix tailTrace_4450249
  have hstable : (prefixWord ++ tailWord_4450249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450249).length < 2 ^ (prefixWord ++ tailWord_4450249).sum := by decide
  have hdescent : baseEnd_4450249 < baseStart_4450249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450260 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4450260 : Nat := 118140960795 + 4450260 * 2 ^ 59
def prefixEnd_4450260 : Nat := 4983230072969 + 3 ^ 40 * 4450260 * 2
def baseEnd_4450260 : Nat := 2285122417477863570983633

theorem tailTrace_4450260 : CollatzResearch.WordTrace tailWord_4450260 prefixEnd_4450260 2285122417477863570983633 := by
  unfold tailWord_4450260
  simp only [CollatzResearch.WordTrace]
  refine ⟨81157158428737769371462117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108209544571650359161949489 81157158428737769371462117)
  ·
    refine ⟨15216967205388331757149147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81157158428737769371462117 15216967205388331757149147)
    ·
      refine ⟨22825450808082497635723721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15216967205388331757149147 22825450808082497635723721)
      ·
        refine ⟨17119088106061873226792791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22825450808082497635723721 17119088106061873226792791)
        ·
          refine ⟨25678632159092809840189187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17119088106061873226792791 25678632159092809840189187)
          ·
            refine ⟨38517948238639214760283781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25678632159092809840189187 38517948238639214760283781)
            ·
              refine ⟨7222115294744852767553209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38517948238639214760283781 7222115294744852767553209)
              ·
                refine ⟨5416586471058639575664907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7222115294744852767553209 5416586471058639575664907)
                ·
                  refine ⟨8124879706587959363497361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416586471058639575664907 8124879706587959363497361)
                  ·
                    refine ⟨6093659779940969522623021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8124879706587959363497361 6093659779940969522623021)
                    ·
                      refine ⟨2285122417477863570983633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093659779940969522623021 2285122417477863570983633)
                      ·
                        rfl

theorem cell23_4450260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4450260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450260 prefixEnd_4450260 := by exact prefixLift 4450260
  have htrace : WordTrace (prefixWord ++ tailWord_4450260) baseStart_4450260 baseEnd_4450260 := by
    simpa [prefixWord, tailWord_4450260, baseEnd_4450260] using wordTrace_append hprefix tailTrace_4450260
  have hstable : (prefixWord ++ tailWord_4450260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450260).length < 2 ^ (prefixWord ++ tailWord_4450260).sum := by decide
  have hdescent : baseEnd_4450260 < baseStart_4450260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450268 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4450268 : Nat := 118140960795 + 4450268 * 2 ^ 59
def prefixEnd_4450268 : Nat := 4983230072969 + 3 ^ 40 * 4450268 * 2
def baseEnd_4450268 : Nat := 2285126525323099539683597

theorem tailTrace_4450268 : CollatzResearch.WordTrace tailWord_4450268 prefixEnd_4450268 2285126525323099539683597 := by
  unfold tailWord_4450268
  simp only [CollatzResearch.WordTrace]
  refine ⟨81157304320723278054607729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108209739094297704072810305 81157304320723278054607729)
  ·
    refine ⟨60867978240542458540955797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81157304320723278054607729 60867978240542458540955797)
    ·
      refine ⟨2853186480025427744107303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60867978240542458540955797 2853186480025427744107303)
      ·
        refine ⟨4279779720038141616160955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853186480025427744107303 4279779720038141616160955)
        ·
          refine ⟨6419669580057212424241433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279779720038141616160955 6419669580057212424241433)
          ·
            refine ⟨4814752185042909318181075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419669580057212424241433 4814752185042909318181075)
            ·
              refine ⟨7222128277564363977271613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814752185042909318181075 7222128277564363977271613)
              ·
                refine ⟨2708298104086636491476855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7222128277564363977271613 2708298104086636491476855)
                ·
                  refine ⟨4062447156129954737215283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708298104086636491476855 4062447156129954737215283)
                  ·
                    refine ⟨6093670734194932105822925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062447156129954737215283 6093670734194932105822925)
                    ·
                      refine ⟨2285126525323099539683597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093670734194932105822925 2285126525323099539683597)
                      ·
                        rfl

theorem cell23_4450268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4450268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450268 prefixEnd_4450268 := by exact prefixLift 4450268
  have htrace : WordTrace (prefixWord ++ tailWord_4450268) baseStart_4450268 baseEnd_4450268 := by
    simpa [prefixWord, tailWord_4450268, baseEnd_4450268] using wordTrace_append hprefix tailTrace_4450268
  have hstable : (prefixWord ++ tailWord_4450268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450268).length < 2 ^ (prefixWord ++ tailWord_4450268).sum := by decide
  have hdescent : baseEnd_4450268 < baseStart_4450268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450273 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_4450273 : Nat := 118140960795 + 4450273 * 2 ^ 59
def prefixEnd_4450273 : Nat := 4983230072969 + 3 ^ 40 * 4450273 * 2
def baseEnd_4450273 : Nat := 2285129092726372020121073

theorem tailTrace_4450273 : CollatzResearch.WordTrace tailWord_4450273 prefixEnd_4450273 2285129092726372020121073 := by
  unfold tailWord_4450273
  simp only [CollatzResearch.WordTrace]
  refine ⟨162314791006428441963147473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108209860670952294642098315 162314791006428441963147473)
  ·
    refine ⟨121736093254821331472360605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162314791006428441963147473 121736093254821331472360605)
    ·
      refine ⟨45651034970557999302135227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121736093254821331472360605 45651034970557999302135227)
      ·
        refine ⟨68476552455836998953202841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45651034970557999302135227 68476552455836998953202841)
        ·
          refine ⟨51357414341877749214902131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68476552455836998953202841 51357414341877749214902131)
          ·
            refine ⟨77036121512816623822353197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51357414341877749214902131 77036121512816623822353197)
            ·
              refine ⟨28888545567306233933382449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77036121512816623822353197 28888545567306233933382449)
              ·
                refine ⟨21666409175479675450036837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28888545567306233933382449 21666409175479675450036837)
                ·
                  refine ⟨4062451720402439146881907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21666409175479675450036837 4062451720402439146881907)
                  ·
                    refine ⟨6093677580603658720322861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062451720402439146881907 6093677580603658720322861)
                    ·
                      refine ⟨2285129092726372020121073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093677580603658720322861 2285129092726372020121073)
                      ·
                        rfl

theorem cell23_4450273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_4450273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450273 prefixEnd_4450273 := by exact prefixLift 4450273
  have htrace : WordTrace (prefixWord ++ tailWord_4450273) baseStart_4450273 baseEnd_4450273 := by
    simpa [prefixWord, tailWord_4450273, baseEnd_4450273] using wordTrace_append hprefix tailTrace_4450273
  have hstable : (prefixWord ++ tailWord_4450273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450273).length < 2 ^ (prefixWord ++ tailWord_4450273).sum := by decide
  have hdescent : baseEnd_4450273 < baseStart_4450273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450316 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4450316 : Nat := 118140960795 + 4450316 * 2 ^ 59
def prefixEnd_4450316 : Nat := 4983230072969 + 3 ^ 40 * 4450316 * 2
def baseEnd_4450316 : Nat := 2285151172394515351883375

theorem tailTrace_4450316 : CollatzResearch.WordTrace tailWord_4450316 prefixEnd_4450316 2285151172394515351883375 := by
  unfold tailWord_4450316
  simp only [CollatzResearch.WordTrace]
  refine ⟨81158179672636330153481401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108210906230181773537975201 81158179672636330153481401)
  ·
    refine ⟨60868634754477247615111051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81158179672636330153481401 60868634754477247615111051)
    ·
      refine ⟨91302952131715871422666577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60868634754477247615111051 91302952131715871422666577)
      ·
        refine ⟨68477214098786903566999933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91302952131715871422666577 68477214098786903566999933)
        ·
          refine ⟨25678955287045088837624975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68477214098786903566999933 25678955287045088837624975)
          ·
            refine ⟨38518432930567633256437463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25678955287045088837624975 38518432930567633256437463)
            ·
              refine ⟨57777649395851449884656195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38518432930567633256437463 57777649395851449884656195)
              ·
                refine ⟨86666474093777174826984293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57777649395851449884656195 86666474093777174826984293)
                ·
                  refine ⟨16249963892583220280059555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86666474093777174826984293 16249963892583220280059555)
                  ·
                    refine ⟨24374945838874830420089333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16249963892583220280059555 24374945838874830420089333)
                    ·
                      refine ⟨2285151172394515351883375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24374945838874830420089333 2285151172394515351883375)
                      ·
                        rfl

theorem cell23_4450316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4450316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450316 prefixEnd_4450316 := by exact prefixLift 4450316
  have htrace : WordTrace (prefixWord ++ tailWord_4450316) baseStart_4450316 baseEnd_4450316 := by
    simpa [prefixWord, tailWord_4450316, baseEnd_4450316] using wordTrace_append hprefix tailTrace_4450316
  have hstable : (prefixWord ++ tailWord_4450316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450316).length < 2 ^ (prefixWord ++ tailWord_4450316).sum := by decide
  have hdescent : baseEnd_4450316 < baseStart_4450316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450330 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_4450330 : Nat := 118140960795 + 4450330 * 2 ^ 59
def prefixEnd_4450330 : Nat := 4983230072969 + 3 ^ 40 * 4450330 * 2
def baseEnd_4450330 : Nat := 2285158361123678297108311

theorem tailTrace_4450330 : CollatzResearch.WordTrace tailWord_4450330 prefixEnd_4450330 2285158361123678297108311 := by
  unfold tailWord_4450330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40579217491805485174493111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108211246644814627131981629 40579217491805485174493111)
  ·
    refine ⟨60868826237708227761739667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40579217491805485174493111 60868826237708227761739667)
    ·
      refine ⟨91303239356562341642609501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60868826237708227761739667 91303239356562341642609501)
      ·
        refine ⟨34238714758710878115978563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91303239356562341642609501 34238714758710878115978563)
        ·
          refine ⟨51358072138066317173967845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34238714758710878115978563 51358072138066317173967845)
          ·
            refine ⟨9629638525887434470118971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51358072138066317173967845 9629638525887434470118971)
            ·
              refine ⟨14444457788831151705178457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9629638525887434470118971 14444457788831151705178457)
              ·
                refine ⟨10833343341623363778883843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14444457788831151705178457 10833343341623363778883843)
                ·
                  refine ⟨16250015012435045668325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10833343341623363778883843 16250015012435045668325765)
                  ·
                    refine ⟨3046877814831571062811081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16250015012435045668325765 3046877814831571062811081)
                    ·
                      refine ⟨2285158361123678297108311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046877814831571062811081 2285158361123678297108311)
                      ·
                        rfl

theorem cell23_4450330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_4450330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450330 prefixEnd_4450330 := by exact prefixLift 4450330
  have htrace : WordTrace (prefixWord ++ tailWord_4450330) baseStart_4450330 baseEnd_4450330 := by
    simpa [prefixWord, tailWord_4450330, baseEnd_4450330] using wordTrace_append hprefix tailTrace_4450330
  have hstable : (prefixWord ++ tailWord_4450330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450330).length < 2 ^ (prefixWord ++ tailWord_4450330).sum := by decide
  have hdescent : baseEnd_4450330 < baseStart_4450330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450333 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4450333 : Nat := 118140960795 + 4450333 * 2 ^ 59
def prefixEnd_4450333 : Nat := 4983230072969 + 3 ^ 40 * 4450333 * 2
def baseEnd_4450333 : Nat := 2285159901565641785370797

theorem tailTrace_4450333 : CollatzResearch.WordTrace tailWord_4450333 prefixEnd_4450333 2285159901565641785370797 := by
  unfold tailWord_4450333
  simp only [CollatzResearch.WordTrace]
  refine ⟨162316979386211072210331653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108211319590807381473554435 162316979386211072210331653)
  ·
    refine ⟨30434433634914576039437185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162316979386211072210331653 30434433634914576039437185)
    ·
      refine ⟨22825825226185932029577889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30434433634914576039437185 22825825226185932029577889)
      ·
        refine ⟨17119368919639449022183417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22825825226185932029577889 17119368919639449022183417)
        ·
          refine ⟨12839526689729586766637563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17119368919639449022183417 12839526689729586766637563)
          ·
            refine ⟨19259290034594380149956345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839526689729586766637563 19259290034594380149956345)
            ·
              refine ⟨14444467525945785112467259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19259290034594380149956345 14444467525945785112467259)
              ·
                refine ⟨21666701288918677668700889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14444467525945785112467259 21666701288918677668700889)
                ·
                  refine ⟨16250025966689008251525667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21666701288918677668700889 16250025966689008251525667)
                  ·
                    refine ⟨24375038950033512377288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16250025966689008251525667 24375038950033512377288501)
                    ·
                      refine ⟨2285159901565641785370797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24375038950033512377288501 2285159901565641785370797)
                      ·
                        rfl

theorem cell23_4450333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4450333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450333 prefixEnd_4450333 := by exact prefixLift 4450333
  have htrace : WordTrace (prefixWord ++ tailWord_4450333) baseStart_4450333 baseEnd_4450333 := by
    simpa [prefixWord, tailWord_4450333, baseEnd_4450333] using wordTrace_append hprefix tailTrace_4450333
  have hstable : (prefixWord ++ tailWord_4450333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450333).length < 2 ^ (prefixWord ++ tailWord_4450333).sum := by decide
  have hdescent : baseEnd_4450333 < baseStart_4450333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450373 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_4450373 : Nat := 118140960795 + 4450373 * 2 ^ 59
def prefixEnd_4450373 : Nat := 4983230072969 + 3 ^ 40 * 4450373 * 2
def baseEnd_4450373 : Nat := 2285180440791821628870613

theorem tailTrace_4450373 : CollatzResearch.WordTrace tailWord_4450373 prefixEnd_4450373 2285180440791821628870613 := by
  unfold tailWord_4450373
  simp only [CollatzResearch.WordTrace]
  refine ⟨162318438306066159041787773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108212292204044106027858515 162318438306066159041787773)
  ·
    refine ⟨60869414364774809640670415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162318438306066159041787773 60869414364774809640670415)
    ·
      refine ⟨91304121547162214461005623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60869414364774809640670415 91304121547162214461005623)
      ·
        refine ⟨136956182320743321691508435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91304121547162214461005623 136956182320743321691508435)
        ·
          refine ⟨205434273481114982537262653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136956182320743321691508435 205434273481114982537262653)
          ·
            refine ⟨77037852555418118451473495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205434273481114982537262653 77037852555418118451473495)
            ·
              refine ⟨115556778833127177677210243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77037852555418118451473495 115556778833127177677210243)
              ·
                refine ⟨173335168249690766515815365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115556778833127177677210243 173335168249690766515815365)
                ·
                  refine ⟨32500344046817018721715381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173335168249690766515815365 32500344046817018721715381)
                  ·
                    refine ⟨3046907254389095505160817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32500344046817018721715381 3046907254389095505160817)
                    ·
                      refine ⟨2285180440791821628870613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046907254389095505160817 2285180440791821628870613)
                      ·
                        rfl

theorem cell23_4450373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_4450373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450373 prefixEnd_4450373 := by exact prefixLift 4450373
  have htrace : WordTrace (prefixWord ++ tailWord_4450373) baseStart_4450373 baseEnd_4450373 := by
    simpa [prefixWord, tailWord_4450373, baseEnd_4450373] using wordTrace_append hprefix tailTrace_4450373
  have hstable : (prefixWord ++ tailWord_4450373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450373).length < 2 ^ (prefixWord ++ tailWord_4450373).sum := by decide
  have hdescent : baseEnd_4450373 < baseStart_4450373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450376 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_4450376 : Nat := 118140960795 + 4450376 * 2 ^ 59
def prefixEnd_4450376 : Nat := 4983230072969 + 3 ^ 40 * 4450376 * 2
def baseEnd_4450376 : Nat := 2285181981233785117133099

theorem tailTrace_4450376 : CollatzResearch.WordTrace tailWord_4450376 prefixEnd_4450376 2285181981233785117133099 := by
  unfold tailWord_4450376
  simp only [CollatzResearch.WordTrace]
  refine ⟨81159273862527645277073491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108212365150036860369431321 81159273862527645277073491)
  ·
    refine ⟨121738910793791467915610237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81159273862527645277073491 121738910793791467915610237)
    ·
      refine ⟨45652091547671800468353839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121738910793791467915610237 45652091547671800468353839)
      ·
        refine ⟨68478137321507700702530759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45652091547671800468353839 68478137321507700702530759)
        ·
          refine ⟨102717205982261551053796139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68478137321507700702530759 102717205982261551053796139)
          ·
            refine ⟨154075808973392326580694209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102717205982261551053796139 154075808973392326580694209)
            ·
              refine ⟨115556856730044244935520657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154075808973392326580694209 115556856730044244935520657)
              ·
                refine ⟨86667642547533183701640493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115556856730044244935520657 86667642547533183701640493)
                ·
                  refine ⟨32500365955324943888115185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86667642547533183701640493 32500365955324943888115185)
                  ·
                    refine ⟨24375274466493707916086389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32500365955324943888115185 24375274466493707916086389)
                    ·
                      refine ⟨2285181981233785117133099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24375274466493707916086389 2285181981233785117133099)
                      ·
                        rfl

theorem cell23_4450376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_4450376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450376 prefixEnd_4450376 := by exact prefixLift 4450376
  have htrace : WordTrace (prefixWord ++ tailWord_4450376) baseStart_4450376 baseEnd_4450376 := by
    simpa [prefixWord, tailWord_4450376, baseEnd_4450376] using wordTrace_append hprefix tailTrace_4450376
  have hstable : (prefixWord ++ tailWord_4450376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450376).length < 2 ^ (prefixWord ++ tailWord_4450376).sum := by decide
  have hdescent : baseEnd_4450376 < baseStart_4450376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450403 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4450403 : Nat := 118140960795 + 4450403 * 2 ^ 59
def prefixEnd_4450403 : Nat := 4983230072969 + 3 ^ 40 * 4450403 * 2
def baseEnd_4450403 : Nat := 2285195845211456511495475

theorem tailTrace_4450403 : CollatzResearch.WordTrace tailWord_4450403 prefixEnd_4450403 2285195845211456511495475 := by
  unfold tailWord_4450403
  simp only [CollatzResearch.WordTrace]
  refine ⟨162319532495957474165379863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108213021663971649443586575 162319532495957474165379863)
  ·
    refine ⟨243479298743936211248069795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162319532495957474165379863 243479298743936211248069795)
    ·
      refine ⟨365218948115904316872104693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243479298743936211248069795 365218948115904316872104693)
      ·
        refine ⟨34239276385866029706759815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 365218948115904316872104693 34239276385866029706759815)
        ·
          refine ⟨51358914578799044560139723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34239276385866029706759815 51358914578799044560139723)
          ·
            refine ⟨77038371868198566840209585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51358914578799044560139723 77038371868198566840209585)
            ·
              refine ⟨57778778901148925130157189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77038371868198566840209585 57778778901148925130157189)
              ·
                refine ⟨10833521043965423461904473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57778778901148925130157189 10833521043965423461904473)
                ·
                  refine ⟨8125140782974067596428355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10833521043965423461904473 8125140782974067596428355)
                  ·
                    refine ⟨12187711174461101394642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8125140782974067596428355 12187711174461101394642533)
                    ·
                      refine ⟨2285195845211456511495475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12187711174461101394642533 2285195845211456511495475)
                      ·
                        rfl

theorem cell23_4450403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4450403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450403 prefixEnd_4450403 := by exact prefixLift 4450403
  have htrace : WordTrace (prefixWord ++ tailWord_4450403) baseStart_4450403 baseEnd_4450403 := by
    simpa [prefixWord, tailWord_4450403, baseEnd_4450403] using wordTrace_append hprefix tailTrace_4450403
  have hstable : (prefixWord ++ tailWord_4450403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450403).length < 2 ^ (prefixWord ++ tailWord_4450403).sum := by decide
  have hdescent : baseEnd_4450403 < baseStart_4450403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450423 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_4450423 : Nat := 118140960795 + 4450423 * 2 ^ 59
def prefixEnd_4450423 : Nat := 4983230072969 + 3 ^ 40 * 4450423 * 2
def baseEnd_4450423 : Nat := 2285206114824546433245383

theorem tailTrace_4450423 : CollatzResearch.WordTrace tailWord_4450423 prefixEnd_4450423 2285206114824546433245383 := by
  unfold tailWord_4450423
  simp only [CollatzResearch.WordTrace]
  refine ⟨162320261955885017581107923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108213507970590011720738615 162320261955885017581107923)
  ·
    refine ⟨243480392933827526371661885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162320261955885017581107923 243480392933827526371661885)
    ·
      refine ⟨91305147350185322389373207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243480392933827526371661885 91305147350185322389373207)
      ·
        refine ⟨136957721025277983584059811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91305147350185322389373207 136957721025277983584059811)
        ·
          refine ⟨205436581537916975376089717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136957721025277983584059811 205436581537916975376089717)
          ·
            refine ⟨19259679519179716441508411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205436581537916975376089717 19259679519179716441508411)
            ·
              refine ⟨28889519278769574662262617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19259679519179716441508411 28889519278769574662262617)
              ·
                refine ⟨21667139459077180996696963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28889519278769574662262617 21667139459077180996696963)
                ·
                  refine ⟨32500709188615771495045445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21667139459077180996696963 32500709188615771495045445)
                  ·
                    refine ⟨6093882972865457155321021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32500709188615771495045445 6093882972865457155321021)
                    ·
                      refine ⟨2285206114824546433245383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093882972865457155321021 2285206114824546433245383)
                      ·
                        rfl

theorem cell23_4450423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_4450423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450423 prefixEnd_4450423 := by exact prefixLift 4450423
  have htrace : WordTrace (prefixWord ++ tailWord_4450423) baseStart_4450423 baseEnd_4450423 := by
    simpa [prefixWord, tailWord_4450423, baseEnd_4450423] using wordTrace_append hprefix tailTrace_4450423
  have hstable : (prefixWord ++ tailWord_4450423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450423).length < 2 ^ (prefixWord ++ tailWord_4450423).sum := by decide
  have hdescent : baseEnd_4450423 < baseStart_4450423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450440 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4450440 : Nat := 118140960795 + 4450440 * 2 ^ 59
def prefixEnd_4450440 : Nat := 4983230072969 + 3 ^ 40 * 4450440 * 2
def baseEnd_4450440 : Nat := 2285214843995672866732805

theorem tailTrace_4450440 : CollatzResearch.WordTrace tailWord_4450440 prefixEnd_4450440 2285214843995672866732805 := by
  unfold tailWord_4450440
  simp only [CollatzResearch.WordTrace]
  refine ⟨81160440998411714742238387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108213921331215619656317849 81160440998411714742238387)
  ·
    refine ⟨121740661497617572113357581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81160440998411714742238387 121740661497617572113357581)
    ·
      refine ⟨45652748061606589542509093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121740661497617572113357581 45652748061606589542509093)
      ·
        refine ⟨8559890261551235539220455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45652748061606589542509093 8559890261551235539220455)
        ·
          refine ⟨12839835392326853308830683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559890261551235539220455 12839835392326853308830683)
          ·
            refine ⟨19259753088490279963246025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839835392326853308830683 19259753088490279963246025)
            ·
              refine ⟨14444814816367709972434519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19259753088490279963246025 14444814816367709972434519)
              ·
                refine ⟨21667222224551564958651779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14444814816367709972434519 21667222224551564958651779)
                ·
                  refine ⟨32500833336827347437977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21667222224551564958651779 32500833336827347437977669)
                  ·
                    refine ⟨6093906250655127644620813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32500833336827347437977669 6093906250655127644620813)
                    ·
                      refine ⟨2285214843995672866732805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6093906250655127644620813 2285214843995672866732805)
                      ·
                        rfl

theorem cell23_4450440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4450440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450440 prefixEnd_4450440 := by exact prefixLift 4450440
  have htrace : WordTrace (prefixWord ++ tailWord_4450440) baseStart_4450440 baseEnd_4450440 := by
    simpa [prefixWord, tailWord_4450440, baseEnd_4450440] using wordTrace_append hprefix tailTrace_4450440
  have hstable : (prefixWord ++ tailWord_4450440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450440).length < 2 ^ (prefixWord ++ tailWord_4450440).sum := by decide
  have hdescent : baseEnd_4450440 < baseStart_4450440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450464 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 1, 4]
def baseStart_4450464 : Nat := 118140960795 + 4450464 * 2 ^ 59
def prefixEnd_4450464 : Nat := 4983230072969 + 3 ^ 40 * 4450464 * 2
def baseEnd_4450464 : Nat := 761742389177126924277565

theorem tailTrace_4450464 : CollatzResearch.WordTrace tailWord_4450464 prefixEnd_4450464 761742389177126924277565 := by
  unfold tailWord_4450464
  simp only [CollatzResearch.WordTrace]
  refine ⟨81160878674368240791675223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108214504899157654388900297 81160878674368240791675223)
  ·
    refine ⟨121741318011552361187512835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81160878674368240791675223 121741318011552361187512835)
    ·
      refine ⟨182611977017328541781269253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121741318011552361187512835 182611977017328541781269253)
      ·
        refine ⟨34239745690749101583987985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182611977017328541781269253 34239745690749101583987985)
        ·
          refine ⟨25679809268061826187990989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34239745690749101583987985 25679809268061826187990989)
          ·
            refine ⟨9629928475523184820496621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25679809268061826187990989 9629928475523184820496621)
            ·
              refine ⟨3611223178321194307686233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9629928475523184820496621 3611223178321194307686233)
              ·
                refine ⟨2708417383740895730764675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611223178321194307686233 2708417383740895730764675)
                ·
                  refine ⟨4062626075611343596147013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708417383740895730764675 4062626075611343596147013)
                  ·
                    refine ⟨761742389177126924277565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4062626075611343596147013 761742389177126924277565)
                    ·
                      rfl

theorem cell23_4450464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_4450464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450464 prefixEnd_4450464 := by exact prefixLift 4450464
  have htrace : WordTrace (prefixWord ++ tailWord_4450464) baseStart_4450464 baseEnd_4450464 := by
    simpa [prefixWord, tailWord_4450464, baseEnd_4450464] using wordTrace_append hprefix tailTrace_4450464
  have hstable : (prefixWord ++ tailWord_4450464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450464).length < 2 ^ (prefixWord ++ tailWord_4450464).sum := by decide
  have hdescent : baseEnd_4450464 < baseStart_4450464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450477 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 6]
def baseStart_4450477 : Nat := 118140960795 + 4450477 * 2 ^ 59
def prefixEnd_4450477 : Nat := 4983230072969 + 3 ^ 40 * 4450477 * 2
def baseEnd_4450477 : Nat := 253914871419987691330015

theorem tailTrace_4450477 : CollatzResearch.WordTrace tailWord_4450477 prefixEnd_4450477 253914871419987691330015 := by
  unfold tailWord_4450477
  simp only [CollatzResearch.WordTrace]
  refine ⟨162322231497689384803573685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108214820998459589869049123 162322231497689384803573685)
  ·
    refine ⟨15217709202908379825335033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162322231497689384803573685 15217709202908379825335033)
    ·
      refine ⟨11413281902181284869001275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15217709202908379825335033 11413281902181284869001275)
      ·
        refine ⟨17119922853271927303501913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11413281902181284869001275 17119922853271927303501913)
        ·
          refine ⟨12839942139953945477626435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17119922853271927303501913 12839942139953945477626435)
          ·
            refine ⟨19259913209930918216439653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839942139953945477626435 19259913209930918216439653)
            ·
              refine ⟨3611233726862047165582435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19259913209930918216439653 3611233726862047165582435)
              ·
                refine ⟨5416850590293070748373653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611233726862047165582435 5416850590293070748373653)
                ·
                  refine ⟨253914871419987691330015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5416850590293070748373653 253914871419987691330015)
                  ·
                    rfl

theorem cell23_4450477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_4450477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450477 prefixEnd_4450477 := by exact prefixLift 4450477
  have htrace : WordTrace (prefixWord ++ tailWord_4450477) baseStart_4450477 baseEnd_4450477 := by
    simpa [prefixWord, tailWord_4450477, baseEnd_4450477] using wordTrace_append hprefix tailTrace_4450477
  have hstable : (prefixWord ++ tailWord_4450477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450477).length < 2 ^ (prefixWord ++ tailWord_4450477).sum := by decide
  have hdescent : baseEnd_4450477 < baseStart_4450477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450490 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_4450490 : Nat := 118140960795 + 4450490 * 2 ^ 59
def prefixEnd_4450490 : Nat := 4983230072969 + 3 ^ 40 * 4450490 * 2
def baseEnd_4450490 : Nat := 761746839342799223702525

theorem tailTrace_4450490 : CollatzResearch.WordTrace tailWord_4450490 prefixEnd_4450490 761746839342799223702525 := by
  unfold tailWord_4450490
  simp only [CollatzResearch.WordTrace]
  refine ⟨40580676411660572005949231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108215137097761525349197949 40580676411660572005949231)
  ·
    refine ⟨60871014617490858008923847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40580676411660572005949231 60871014617490858008923847)
    ·
      refine ⟨91306521926236287013385771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60871014617490858008923847 91306521926236287013385771)
      ·
        refine ⟨136959782889354430520078657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91306521926236287013385771 136959782889354430520078657)
        ·
          refine ⟨102719837167015822890058993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136959782889354430520078657 102719837167015822890058993)
          ·
            refine ⟨77039877875261867167544245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102719837167015822890058993 77039877875261867167544245)
            ·
              refine ⟨7222488550805800046957273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77039877875261867167544245 7222488550805800046957273)
              ·
                refine ⟨5416866413104350035217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7222488550805800046957273 5416866413104350035217955)
                ·
                  refine ⟨8125299619656525052826933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416866413104350035217955 8125299619656525052826933)
                  ·
                    refine ⟨761746839342799223702525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8125299619656525052826933 761746839342799223702525)
                    ·
                      rfl

theorem cell23_4450490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_4450490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450490 prefixEnd_4450490 := by exact prefixLift 4450490
  have htrace : WordTrace (prefixWord ++ tailWord_4450490) baseStart_4450490 baseEnd_4450490 := by
    simpa [prefixWord, tailWord_4450490, baseEnd_4450490] using wordTrace_append hprefix tailTrace_4450490
  have hstable : (prefixWord ++ tailWord_4450490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450490).length < 2 ^ (prefixWord ++ tailWord_4450490).sum := by decide
  have hdescent : baseEnd_4450490 < baseStart_4450490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450527 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 3, 2, 2]
def baseStart_4450527 : Nat := 118140960795 + 4450527 * 2 ^ 59
def prefixEnd_4450527 : Nat := 4983230072969 + 3 ^ 40 * 4450527 * 2
def baseEnd_4450527 : Nat := 2285259516812614026344905

theorem tailTrace_4450527 : CollatzResearch.WordTrace tailWord_4450527 prefixEnd_4450527 2285259516812614026344905 := by
  unfold tailWord_4450527
  simp only [CollatzResearch.WordTrace]
  refine ⟨162324055147508243342893835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108216036765005495561929223 162324055147508243342893835)
  ·
    refine ⟨243486082721262365014340753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162324055147508243342893835 243486082721262365014340753)
    ·
      refine ⟨182614562040946773760755565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243486082721262365014340753 182614562040946773760755565)
      ·
        refine ⟨68480460765355040160283337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182614562040946773760755565 68480460765355040160283337)
        ·
          refine ⟨51360345574016280120212503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68480460765355040160283337 51360345574016280120212503)
          ·
            refine ⟨77040518361024420180318755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51360345574016280120212503 77040518361024420180318755)
            ·
              refine ⟨115560777541536630270478133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77040518361024420180318755 115560777541536630270478133)
              ·
                refine ⟨10833822894519059087857325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115560777541536630270478133 10833822894519059087857325)
                ·
                  refine ⟨4062683585444647157946497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10833822894519059087857325 4062683585444647157946497)
                  ·
                    refine ⟨3047012689083485368459873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062683585444647157946497 3047012689083485368459873)
                    ·
                      refine ⟨2285259516812614026344905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047012689083485368459873 2285259516812614026344905)
                      ·
                        rfl

theorem cell23_4450527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_4450527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450527 prefixEnd_4450527 := by exact prefixLift 4450527
  have htrace : WordTrace (prefixWord ++ tailWord_4450527) baseStart_4450527 baseEnd_4450527 := by
    simpa [prefixWord, tailWord_4450527, baseEnd_4450527] using wordTrace_append hprefix tailTrace_4450527
  have hstable : (prefixWord ++ tailWord_4450527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450527).length < 2 ^ (prefixWord ++ tailWord_4450527).sum := by decide
  have hdescent : baseEnd_4450527 < baseStart_4450527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450540 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_4450540 : Nat := 118140960795 + 4450540 * 2 ^ 59
def prefixEnd_4450540 : Nat := 4983230072969 + 3 ^ 40 * 4450540 * 2
def baseEnd_4450540 : Nat := 2285266192061122475482345

theorem tailTrace_4450540 : CollatzResearch.WordTrace tailWord_4450540 prefixEnd_4450540 2285266192061122475482345 := by
  unfold tailWord_4450540
  simp only [CollatzResearch.WordTrace]
  refine ⟨81162264648230573281558537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108216352864307431042078049 81162264648230573281558537)
  ·
    refine ⟨60871698486172929961168903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81162264648230573281558537 60871698486172929961168903)
    ·
      refine ⟨91307547729259394941753355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60871698486172929961168903 91307547729259394941753355)
      ·
        refine ⟨136961321593889092412630033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91307547729259394941753355 136961321593889092412630033)
        ·
          refine ⟨102720991195416819309472525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136961321593889092412630033 102720991195416819309472525)
          ·
            refine ⟨38520371698281307241052197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102720991195416819309472525 38520371698281307241052197)
            ·
              refine ⟨7222569693427745107697287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38520371698281307241052197 7222569693427745107697287)
              ·
                refine ⟨10833854540141617661545931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222569693427745107697287 10833854540141617661545931)
                ·
                  refine ⟨16250781810212426492318897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10833854540141617661545931 16250781810212426492318897)
                  ·
                    refine ⟨12188086357659319869239173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16250781810212426492318897 12188086357659319869239173)
                    ·
                      refine ⟨2285266192061122475482345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12188086357659319869239173 2285266192061122475482345)
                      ·
                        rfl

theorem cell23_4450540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_4450540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450540 prefixEnd_4450540 := by exact prefixLift 4450540
  have htrace : WordTrace (prefixWord ++ tailWord_4450540) baseStart_4450540 baseEnd_4450540 := by
    simpa [prefixWord, tailWord_4450540, baseEnd_4450540] using wordTrace_append hprefix tailTrace_4450540
  have hstable : (prefixWord ++ tailWord_4450540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450540).length < 2 ^ (prefixWord ++ tailWord_4450540).sum := by decide
  have hdescent : baseEnd_4450540 < baseStart_4450540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450560 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_4450560 : Nat := 118140960795 + 4450560 * 2 ^ 59
def prefixEnd_4450560 : Nat := 4983230072969 + 3 ^ 40 * 4450560 * 2
def baseEnd_4450560 : Nat := 2285276461674212397232253

theorem tailTrace_4450560 : CollatzResearch.WordTrace tailWord_4450560 prefixEnd_4450560 2285276461674212397232253 := by
  unfold tailWord_4450560
  simp only [CollatzResearch.WordTrace]
  refine ⟨81162629378194344989422567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108216839170925793319230089 81162629378194344989422567)
  ·
    refine ⟨121743944067291517484133851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81162629378194344989422567 121743944067291517484133851)
    ·
      refine ⟨182615916100937276226200777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121743944067291517484133851 182615916100937276226200777)
      ·
        refine ⟨136961937075702957169650583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182615916100937276226200777 136961937075702957169650583)
        ·
          refine ⟨205442905613554435754475875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136961937075702957169650583 205442905613554435754475875)
          ·
            refine ⟨308164358420331653631713813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205442905613554435754475875 308164358420331653631713813)
            ·
              refine ⟨14445204300953046263986585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 308164358420331653631713813 14445204300953046263986585)
              ·
                refine ⟨10833903225714784697989939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14445204300953046263986585 10833903225714784697989939)
                ·
                  refine ⟨16250854838572177046984909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10833903225714784697989939 16250854838572177046984909)
                  ·
                    refine ⟨6094070564464566392619341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16250854838572177046984909 6094070564464566392619341)
                    ·
                      refine ⟨2285276461674212397232253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094070564464566392619341 2285276461674212397232253)
                      ·
                        rfl

theorem cell23_4450560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_4450560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450560 prefixEnd_4450560 := by exact prefixLift 4450560
  have htrace : WordTrace (prefixWord ++ tailWord_4450560) baseStart_4450560 baseEnd_4450560 := by
    simpa [prefixWord, tailWord_4450560, baseEnd_4450560] using wordTrace_append hprefix tailTrace_4450560
  have hstable : (prefixWord ++ tailWord_4450560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450560).length < 2 ^ (prefixWord ++ tailWord_4450560).sum := by decide
  have hdescent : baseEnd_4450560 < baseStart_4450560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450561 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_4450561 : Nat := 118140960795 + 4450561 * 2 ^ 59
def prefixEnd_4450561 : Nat := 4983230072969 + 3 ^ 40 * 4450561 * 2
def baseEnd_4450561 : Nat := 2285276975154866893319749

theorem tailTrace_4450561 : CollatzResearch.WordTrace tailWord_4450561 prefixEnd_4450561 2285276975154866893319749 := by
  unfold tailWord_4450561
  simp only [CollatzResearch.WordTrace]
  refine ⟨162325295229385067149631537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108216863486256711433087691 162325295229385067149631537)
  ·
    refine ⟨121743971422038800362223653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162325295229385067149631537 121743971422038800362223653)
    ·
      refine ⟨22826994641632275067916935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121743971422038800362223653 22826994641632275067916935)
      ·
        refine ⟨34240491962448412601875403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22826994641632275067916935 34240491962448412601875403)
        ·
          refine ⟨51360737943672618902813105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34240491962448412601875403 51360737943672618902813105)
          ·
            refine ⟨38520553457754464177109829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51360737943672618902813105 38520553457754464177109829)
            ·
              refine ⟨7222603773328962033208093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38520553457754464177109829 7222603773328962033208093)
              ·
                refine ⟨2708476414998360762453035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7222603773328962033208093 2708476414998360762453035)
                ·
                  refine ⟨4062714622497541143679553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708476414998360762453035 4062714622497541143679553)
                  ·
                    refine ⟨3047035966873155857759665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062714622497541143679553 3047035966873155857759665)
                    ·
                      refine ⟨2285276975154866893319749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047035966873155857759665 2285276975154866893319749)
                      ·
                        rfl

theorem cell23_4450561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_4450561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450561 prefixEnd_4450561 := by exact prefixLift 4450561
  have htrace : WordTrace (prefixWord ++ tailWord_4450561) baseStart_4450561 baseEnd_4450561 := by
    simpa [prefixWord, tailWord_4450561, baseEnd_4450561] using wordTrace_append hprefix tailTrace_4450561
  have hstable : (prefixWord ++ tailWord_4450561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450561).length < 2 ^ (prefixWord ++ tailWord_4450561).sum := by decide
  have hdescent : baseEnd_4450561 < baseStart_4450561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450564 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_4450564 : Nat := 118140960795 + 4450564 * 2 ^ 59
def prefixEnd_4450564 : Nat := 4983230072969 + 3 ^ 40 * 4450564 * 2
def baseEnd_4450564 : Nat := 2285278515596830381582235

theorem tailTrace_4450564 : CollatzResearch.WordTrace tailWord_4450564 prefixEnd_4450564 2285278515596830381582235 := by
  unfold tailWord_4450564
  simp only [CollatzResearch.WordTrace]
  refine ⟨81162702324187099330995373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108216936432249465774660497 81162702324187099330995373)
  ·
    refine ⟨30436013371570162249123265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81162702324187099330995373 30436013371570162249123265)
    ·
      refine ⟨22827010028677621686842449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30436013371570162249123265 22827010028677621686842449)
      ·
        refine ⟨17120257521508216265131837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22827010028677621686842449 17120257521508216265131837)
        ·
          refine ⟨6420096570565581099424439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17120257521508216265131837 6420096570565581099424439)
          ·
            refine ⟨9630144855848371649136659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420096570565581099424439 9630144855848371649136659)
            ·
              refine ⟨14445217283772557473704989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9630144855848371649136659 14445217283772557473704989)
              ·
                refine ⟨5416956481414709052639371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14445217283772557473704989 5416956481414709052639371)
                ·
                  refine ⟨8125434722122063578959057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416956481414709052639371 8125434722122063578959057)
                  ·
                    refine ⟨6094076041591547684219293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8125434722122063578959057 6094076041591547684219293)
                    ·
                      refine ⟨2285278515596830381582235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094076041591547684219293 2285278515596830381582235)
                      ·
                        rfl

theorem cell23_4450564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_4450564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450564 prefixEnd_4450564 := by exact prefixLift 4450564
  have htrace : WordTrace (prefixWord ++ tailWord_4450564) baseStart_4450564 baseEnd_4450564 := by
    simpa [prefixWord, tailWord_4450564, baseEnd_4450564] using wordTrace_append hprefix tailTrace_4450564
  have hstable : (prefixWord ++ tailWord_4450564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450564).length < 2 ^ (prefixWord ++ tailWord_4450564).sum := by decide
  have hdescent : baseEnd_4450564 < baseStart_4450564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450577 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_4450577 : Nat := 118140960795 + 4450577 * 2 ^ 59
def prefixEnd_4450577 : Nat := 4983230072969 + 3 ^ 40 * 4450577 * 2
def baseEnd_4450577 : Nat := 2285285190845338830719675

theorem tailTrace_4450577 : CollatzResearch.WordTrace tailWord_4450577 prefixEnd_4450577 2285285190845338830719675 := by
  unfold tailWord_4450577
  simp only [CollatzResearch.WordTrace]
  refine ⟨162325878797327101882213985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108217252531551401254809323 162325878797327101882213985)
  ·
    refine ⟨121744409097995326411660489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162325878797327101882213985 121744409097995326411660489)
    ·
      refine ⟨91308306823496494808745367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121744409097995326411660489 91308306823496494808745367)
      ·
        refine ⟨136962460235244742213118051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91308306823496494808745367 136962460235244742213118051)
        ·
          refine ⟨205443690352867113319677077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136962460235244742213118051 205443690352867113319677077)
          ·
            refine ⟨9630172985290645936859863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205443690352867113319677077 9630172985290645936859863)
            ·
              refine ⟨14445259477935968905289795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9630172985290645936859863 14445259477935968905289795)
              ·
                refine ⟨21667889216903953357934693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14445259477935968905289795 21667889216903953357934693)
                ·
                  refine ⟨4062729228169491254612755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21667889216903953357934693 4062729228169491254612755)
                  ·
                    refine ⟨6094093842254236881919133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062729228169491254612755 6094093842254236881919133)
                    ·
                      refine ⟨2285285190845338830719675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094093842254236881919133 2285285190845338830719675)
                      ·
                        rfl

theorem cell23_4450577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_4450577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450577 prefixEnd_4450577 := by exact prefixLift 4450577
  have htrace : WordTrace (prefixWord ++ tailWord_4450577) baseStart_4450577 baseEnd_4450577 := by
    simpa [prefixWord, tailWord_4450577, baseEnd_4450577] using wordTrace_append hprefix tailTrace_4450577
  have hstable : (prefixWord ++ tailWord_4450577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450577).length < 2 ^ (prefixWord ++ tailWord_4450577).sum := by decide
  have hdescent : baseEnd_4450577 < baseStart_4450577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450594 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_4450594 : Nat := 118140960795 + 4450594 * 2 ^ 59
def prefixEnd_4450594 : Nat := 4983230072969 + 3 ^ 40 * 4450594 * 2
def baseEnd_4450594 : Nat := 2285293920016465264207097

theorem tailTrace_4450594 : CollatzResearch.WordTrace tailWord_4450594 prefixEnd_4450594 2285293920016465264207097 := by
  unfold tailWord_4450594
  simp only [CollatzResearch.WordTrace]
  refine ⟨40581624709566378446395709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108217665892177009190388557 40581624709566378446395709)
  ·
    refine ⟨15218109266087391917398391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40581624709566378446395709 15218109266087391917398391)
    ·
      refine ⟨22827163899131087876097587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15218109266087391917398391 22827163899131087876097587)
      ·
        refine ⟨34240745848696631814146381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22827163899131087876097587 34240745848696631814146381)
        ·
          refine ⟨12840279693261236930304893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34240745848696631814146381 12840279693261236930304893)
          ·
            refine ⟨4815104884972963848864335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12840279693261236930304893 4815104884972963848864335)
            ·
              refine ⟨7222657327459445773296503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815104884972963848864335 7222657327459445773296503)
              ·
                refine ⟨10833985991189168659944755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222657327459445773296503 10833985991189168659944755)
                ·
                  refine ⟨16250978986783752989917133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10833985991189168659944755 16250978986783752989917133)
                  ·
                    refine ⟨6094117120043907371218925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16250978986783752989917133 6094117120043907371218925)
                    ·
                      refine ⟨2285293920016465264207097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094117120043907371218925 2285293920016465264207097)
                      ·
                        rfl

theorem cell23_4450594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_4450594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450594 prefixEnd_4450594 := by exact prefixLift 4450594
  have htrace : WordTrace (prefixWord ++ tailWord_4450594) baseStart_4450594 baseEnd_4450594 := by
    simpa [prefixWord, tailWord_4450594, baseEnd_4450594] using wordTrace_append hprefix tailTrace_4450594
  have hstable : (prefixWord ++ tailWord_4450594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450594).length < 2 ^ (prefixWord ++ tailWord_4450594).sum := by decide
  have hdescent : baseEnd_4450594 < baseStart_4450594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450620 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_4450620 : Nat := 118140960795 + 4450620 * 2 ^ 59
def prefixEnd_4450620 : Nat := 4983230072969 + 3 ^ 40 * 4450620 * 2
def baseEnd_4450620 : Nat := 2285307270513482162481977

theorem tailTrace_4450620 : CollatzResearch.WordTrace tailWord_4450620 prefixEnd_4450620 2285307270513482162481977 := by
  unfold tailWord_4450620
  simp only [CollatzResearch.WordTrace]
  refine ⟨81163723568085660113014657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108218298090780880150686209 81163723568085660113014657)
  ·
    refine ⟨60872792676064245084760993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81163723568085660113014657 60872792676064245084760993)
    ·
      refine ⟨45654594507048183813570745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60872792676064245084760993 45654594507048183813570745)
      ·
        refine ⟨34240945880286137860178059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45654594507048183813570745 34240945880286137860178059)
        ·
          refine ⟨51361418820429206790267089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34240945880286137860178059 51361418820429206790267089)
          ·
            refine ⟨38521064115321905092700317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51361418820429206790267089 38521064115321905092700317)
            ·
              refine ⟨14445399043245714409762619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38521064115321905092700317 14445399043245714409762619)
              ·
                refine ⟨21668098564868571614643929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14445399043245714409762619 21668098564868571614643929)
                ·
                  refine ⟨16251073923651428710982947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21668098564868571614643929 16251073923651428710982947)
                  ·
                    refine ⟨24376610885477143066474421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16251073923651428710982947 24376610885477143066474421)
                    ·
                      refine ⟨2285307270513482162481977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24376610885477143066474421 2285307270513482162481977)
                      ·
                        rfl

theorem cell23_4450620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_4450620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450620 prefixEnd_4450620 := by exact prefixLift 4450620
  have htrace : WordTrace (prefixWord ++ tailWord_4450620) baseStart_4450620 baseEnd_4450620 := by
    simpa [prefixWord, tailWord_4450620, baseEnd_4450620] using wordTrace_append hprefix tailTrace_4450620
  have hstable : (prefixWord ++ tailWord_4450620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450620).length < 2 ^ (prefixWord ++ tailWord_4450620).sum := by decide
  have hdescent : baseEnd_4450620 < baseStart_4450620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450633 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_4450633 : Nat := 118140960795 + 4450633 * 2 ^ 59
def prefixEnd_4450633 : Nat := 4983230072969 + 3 ^ 40 * 4450633 * 2
def baseEnd_4450633 : Nat := 2285313945761990611619417

theorem tailTrace_4450633 : CollatzResearch.WordTrace tailWord_4450633 prefixEnd_4450633 2285313945761990611619417 := by
  unfold tailWord_4450633
  simp only [CollatzResearch.WordTrace]
  refine ⟨162327921285124223446252553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108218614190082815630835035 162327921285124223446252553)
  ·
    refine ⟨121745940963843167584689415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162327921285124223446252553 121745940963843167584689415)
    ·
      refine ⟨182618911445764751377034123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121745940963843167584689415 182618911445764751377034123)
      ·
        refine ⟨273928367168647127065551185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182618911445764751377034123 273928367168647127065551185)
        ·
          refine ⟨205446275376485345299163389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273928367168647127065551185 205446275376485345299163389)
          ·
            refine ⟨77042353266182004487186271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205446275376485345299163389 77042353266182004487186271)
            ·
              refine ⟨115563529899273006730779407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77042353266182004487186271 115563529899273006730779407)
              ·
                refine ⟨173345294848909510096169111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115563529899273006730779407 173345294848909510096169111)
                ·
                  refine ⟨260017942273364265144253667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173345294848909510096169111 260017942273364265144253667)
                  ·
                    refine ⟨390026913410046397716380501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260017942273364265144253667 390026913410046397716380501)
                    ·
                      refine ⟨2285313945761990611619417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 390026913410046397716380501 2285313945761990611619417)
                      ·
                        rfl

theorem cell23_4450633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_4450633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450633 prefixEnd_4450633 := by exact prefixLift 4450633
  have htrace : WordTrace (prefixWord ++ tailWord_4450633) baseStart_4450633 baseEnd_4450633 := by
    simpa [prefixWord, tailWord_4450633, baseEnd_4450633] using wordTrace_append hprefix tailTrace_4450633
  have hstable : (prefixWord ++ tailWord_4450633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450633).length < 2 ^ (prefixWord ++ tailWord_4450633).sum := by decide
  have hdescent : baseEnd_4450633 < baseStart_4450633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450640 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 7]
def baseStart_4450640 : Nat := 118140960795 + 4450640 * 2 ^ 59
def prefixEnd_4450640 : Nat := 4983230072969 + 3 ^ 40 * 4450640 * 2
def baseEnd_4450640 : Nat := 253924171125174676025765

theorem tailTrace_4450640 : CollatzResearch.WordTrace tailWord_4450640 prefixEnd_4450640 253924171125174676025765 := by
  unfold tailWord_4450640
  simp only [CollatzResearch.WordTrace]
  refine ⟨81164088298049431820878687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108218784397399242427838249 81164088298049431820878687)
  ·
    refine ⟨121746132447074147731318031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81164088298049431820878687 121746132447074147731318031)
    ·
      refine ⟨182619198670611221596977047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121746132447074147731318031 182619198670611221596977047)
      ·
        refine ⟨273928798005916832395465571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182619198670611221596977047 273928798005916832395465571)
        ·
          refine ⟨410893197008875248593198357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273928798005916832395465571 410893197008875248593198357)
          ·
            refine ⟨19260618609791027277806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 410893197008875248593198357 19260618609791027277806173)
            ·
              refine ⟨7222731978671635229177315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19260618609791027277806173 7222731978671635229177315)
              ·
                refine ⟨10834097968007452843765973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222731978671635229177315 10834097968007452843765973)
                ·
                  refine ⟨253924171125174676025765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10834097968007452843765973 253924171125174676025765)
                  ·
                    rfl

theorem cell23_4450640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_4450640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450640 prefixEnd_4450640 := by exact prefixLift 4450640
  have htrace : WordTrace (prefixWord ++ tailWord_4450640) baseStart_4450640 baseEnd_4450640 := by
    simpa [prefixWord, tailWord_4450640, baseEnd_4450640] using wordTrace_append hprefix tailTrace_4450640
  have hstable : (prefixWord ++ tailWord_4450640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450640).length < 2 ^ (prefixWord ++ tailWord_4450640).sum := by decide
  have hdescent : baseEnd_4450640 < baseStart_4450640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450643 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_4450643 : Nat := 118140960795 + 4450643 * 2 ^ 59
def prefixEnd_4450643 : Nat := 4983230072969 + 3 ^ 40 * 4450643 * 2
def baseEnd_4450643 : Nat := 2285319080568535572494371

theorem tailTrace_4450643 : CollatzResearch.WordTrace tailWord_4450643 prefixEnd_4450643 2285319080568535572494371 := by
  unfold tailWord_4450643
  simp only [CollatzResearch.WordTrace]
  refine ⟨162328286015087995154116583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108218857343391996769411055 162328286015087995154116583)
  ·
    refine ⟨243492429022631992731174875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162328286015087995154116583 243492429022631992731174875)
    ·
      refine ⟨365238643533947989096762313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243492429022631992731174875 365238643533947989096762313)
      ·
        refine ⟨273928982650460991822571735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365238643533947989096762313 273928982650460991822571735)
        ·
          refine ⟨410893473975691487733857603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273928982650460991822571735 410893473975691487733857603)
          ·
            refine ⟨616340210963537231600786405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410893473975691487733857603 616340210963537231600786405)
            ·
              refine ⟨115563789555663230925147451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 616340210963537231600786405 115563789555663230925147451)
              ·
                refine ⟨173345684333494846387721177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115563789555663230925147451 173345684333494846387721177)
                ·
                  refine ⟨130009263250121134790790883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173345684333494846387721177 130009263250121134790790883)
                  ·
                    refine ⟨195013894875181702186186325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130009263250121134790790883 195013894875181702186186325)
                    ·
                      refine ⟨2285319080568535572494371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 195013894875181702186186325 2285319080568535572494371)
                      ·
                        rfl

theorem cell23_4450643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_4450643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450643 prefixEnd_4450643 := by exact prefixLift 4450643
  have htrace : WordTrace (prefixWord ++ tailWord_4450643) baseStart_4450643 baseEnd_4450643 := by
    simpa [prefixWord, tailWord_4450643, baseEnd_4450643] using wordTrace_append hprefix tailTrace_4450643
  have hstable : (prefixWord ++ tailWord_4450643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450643).length < 2 ^ (prefixWord ++ tailWord_4450643).sum := by decide
  have hdescent : baseEnd_4450643 < baseStart_4450643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450650 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_4450650 : Nat := 118140960795 + 4450650 * 2 ^ 59
def prefixEnd_4450650 : Nat := 4983230072969 + 3 ^ 40 * 4450650 * 2
def baseEnd_4450650 : Nat := 2285322674933117045106839

theorem tailTrace_4450650 : CollatzResearch.WordTrace tailWord_4450650 prefixEnd_4450650 2285322674933117045106839 := by
  unfold tailWord_4450650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40582135331515658837405351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108219027550708423566414269 40582135331515658837405351)
  ·
    refine ⟨60873202997273488256108027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40582135331515658837405351 60873202997273488256108027)
    ·
      refine ⟨91309804495910232384162041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60873202997273488256108027 91309804495910232384162041)
      ·
        refine ⟨68482353371932674288121531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91309804495910232384162041 68482353371932674288121531)
        ·
          refine ⟨102723530057899011432182297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68482353371932674288121531 102723530057899011432182297)
          ·
            refine ⟨77042647543424258574136723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102723530057899011432182297 77042647543424258574136723)
            ·
              refine ⟨115563971315136387861205085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77042647543424258574136723 115563971315136387861205085)
              ·
                refine ⟨43336489243176145447951907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115563971315136387861205085 43336489243176145447951907)
                ·
                  refine ⟨65004733864764218171927861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43336489243176145447951907 65004733864764218171927861)
                  ·
                    refine ⟨6094193799821645453618237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65004733864764218171927861 6094193799821645453618237)
                    ·
                      refine ⟨2285322674933117045106839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094193799821645453618237 2285322674933117045106839)
                      ·
                        rfl

theorem cell23_4450650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_4450650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450650 prefixEnd_4450650 := by exact prefixLift 4450650
  have htrace : WordTrace (prefixWord ++ tailWord_4450650) baseStart_4450650 baseEnd_4450650 := by
    simpa [prefixWord, tailWord_4450650, baseEnd_4450650] using wordTrace_append hprefix tailTrace_4450650
  have hstable : (prefixWord ++ tailWord_4450650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450650).length < 2 ^ (prefixWord ++ tailWord_4450650).sum := by decide
  have hdescent : baseEnd_4450650 < baseStart_4450650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450691 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 5]
def baseStart_4450691 : Nat := 118140960795 + 4450691 * 2 ^ 59
def prefixEnd_4450691 : Nat := 4983230072969 + 3 ^ 40 * 4450691 * 2
def baseEnd_4450691 : Nat := 253927080848883487188239

theorem tailTrace_4450691 : CollatzResearch.WordTrace tailWord_4450691 prefixEnd_4450691 253927080848883487188239 := by
  unfold tailWord_4450691
  simp only [CollatzResearch.WordTrace]
  refine ⟨162330036718914099351863927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108220024479276066234575951 162330036718914099351863927)
  ·
    refine ⟨243495055078371149027795891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162330036718914099351863927 243495055078371149027795891)
    ·
      refine ⟨365242582617556723541693837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243495055078371149027795891 365242582617556723541693837)
      ·
        refine ⟨136965968481583771328135189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365242582617556723541693837 136965968481583771328135189)
        ·
          refine ⟨6420279772574239281006337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136965968481583771328135189 6420279772574239281006337)
          ·
            refine ⟨4815209829430679460754753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6420279772574239281006337 4815209829430679460754753)
            ·
              refine ⟨3611407372073009595566065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4815209829430679460754753 3611407372073009595566065)
              ·
                refine ⟨2708555529054757196674549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611407372073009595566065 2708555529054757196674549)
                ·
                  refine ⟨253927080848883487188239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708555529054757196674549 253927080848883487188239)
                  ·
                    rfl

theorem cell23_4450691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 5].length) (baseStart_4450691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450691 prefixEnd_4450691 := by exact prefixLift 4450691
  have htrace : WordTrace (prefixWord ++ tailWord_4450691) baseStart_4450691 baseEnd_4450691 := by
    simpa [prefixWord, tailWord_4450691, baseEnd_4450691] using wordTrace_append hprefix tailTrace_4450691
  have hstable : (prefixWord ++ tailWord_4450691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450691).length < 2 ^ (prefixWord ++ tailWord_4450691).sum := by decide
  have hdescent : baseEnd_4450691 < baseStart_4450691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450721 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4450721 : Nat := 118140960795 + 4450721 * 2 ^ 59
def prefixEnd_4450721 : Nat := 4983230072969 + 3 ^ 40 * 4450721 * 2
def baseEnd_4450721 : Nat := 761786377353195422439671

theorem tailTrace_4450721 : CollatzResearch.WordTrace tailWord_4450721 prefixEnd_4450721 761786377353195422439671 := by
  unfold tailWord_4450721
  simp only [CollatzResearch.WordTrace]
  refine ⟨162331130908805414475456017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108220753939203609650304011 162331130908805414475456017)
  ·
    refine ⟨121748348181604060856592013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162331130908805414475456017 121748348181604060856592013)
    ·
      refine ⟨45655630568101522821222005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121748348181604060856592013 45655630568101522821222005)
      ·
        refine ⟨4280215365759517764489563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45655630568101522821222005 4280215365759517764489563)
        ·
          refine ⟨6420323048639276646734345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280215365759517764489563 6420323048639276646734345)
          ·
            refine ⟨4815242286479457485050759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6420323048639276646734345 4815242286479457485050759)
            ·
              refine ⟨7222863429719186227576139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815242286479457485050759 7222863429719186227576139)
              ·
                refine ⟨10834295144578779341364209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222863429719186227576139 10834295144578779341364209)
                ·
                  refine ⟨8125721358434084506023157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10834295144578779341364209 8125721358434084506023157)
                  ·
                    refine ⟨761786377353195422439671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8125721358434084506023157 761786377353195422439671)
                    ·
                      rfl

theorem cell23_4450721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4450721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450721 prefixEnd_4450721 := by exact prefixLift 4450721
  have htrace : WordTrace (prefixWord ++ tailWord_4450721) baseStart_4450721 baseEnd_4450721 := by
    simpa [prefixWord, tailWord_4450721, baseEnd_4450721] using wordTrace_append hprefix tailTrace_4450721
  have hstable : (prefixWord ++ tailWord_4450721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450721).length < 2 ^ (prefixWord ++ tailWord_4450721).sum := by decide
  have hdescent : baseEnd_4450721 < baseStart_4450721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450774 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4450774 : Nat := 118140960795 + 4450774 * 2 ^ 59
def prefixEnd_4450774 : Nat := 4983230072969 + 3 ^ 40 * 4450774 * 2
def baseEnd_4450774 : Nat := 2285386346534274559956269

theorem tailTrace_4450774 : CollatzResearch.WordTrace tailWord_4450774 prefixEnd_4450774 2285386346534274559956269 := by
  unfold tailWord_4450774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145816498600837782945961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108222042651742269684756917 10145816498600837782945961)
  ·
    refine ⟨7609362373950628337209471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10145816498600837782945961 7609362373950628337209471)
    ·
      refine ⟨11414043560925942505814207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7609362373950628337209471 11414043560925942505814207)
      ·
        refine ⟨17121065341388913758721311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11414043560925942505814207 17121065341388913758721311)
        ·
          refine ⟨25681598012083370638081967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17121065341388913758721311 25681598012083370638081967)
          ·
            refine ⟨38522397018125055957122951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25681598012083370638081967 38522397018125055957122951)
            ·
              refine ⟨57783595527187583935684427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38522397018125055957122951 57783595527187583935684427)
              ·
                refine ⟨86675393290781375903526641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57783595527187583935684427 86675393290781375903526641)
                ·
                  refine ⟨65006544968086031927644981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86675393290781375903526641 65006544968086031927644981)
                  ·
                    refine ⟨6094363590758065493216717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65006544968086031927644981 6094363590758065493216717)
                    ·
                      refine ⟨2285386346534274559956269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094363590758065493216717 2285386346534274559956269)
                      ·
                        rfl

theorem cell23_4450774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4450774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450774 prefixEnd_4450774 := by exact prefixLift 4450774
  have htrace : WordTrace (prefixWord ++ tailWord_4450774) baseStart_4450774 baseEnd_4450774 := by
    simpa [prefixWord, tailWord_4450774, baseEnd_4450774] using wordTrace_append hprefix tailTrace_4450774
  have hstable : (prefixWord ++ tailWord_4450774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450774).length < 2 ^ (prefixWord ++ tailWord_4450774).sum := by decide
  have hdescent : baseEnd_4450774 < baseStart_4450774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450784 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2]
def baseStart_4450784 : Nat := 118140960795 + 4450784 * 2 ^ 59
def prefixEnd_4450784 : Nat := 4983230072969 + 3 ^ 40 * 4450784 * 2
def baseEnd_4450784 : Nat := 2285391481340819520831223

theorem tailTrace_4450784 : CollatzResearch.WordTrace tailWord_4450784 prefixEnd_4450784 2285391481340819520831223 := by
  unfold tailWord_4450784
  simp only [CollatzResearch.WordTrace]
  refine ⟨81166714353788588117499703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108222285805051450823332937 81166714353788588117499703)
  ·
    refine ⟨121750071530682882176249555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81166714353788588117499703 121750071530682882176249555)
    ·
      refine ⟨182625107296024323264374333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121750071530682882176249555 182625107296024323264374333)
      ·
        refine ⟨68484415236009121224140375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182625107296024323264374333 68484415236009121224140375)
        ·
          refine ⟨102726622854013681836210563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68484415236009121224140375 102726622854013681836210563)
          ·
            refine ⟨154089934281020522754315845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102726622854013681836210563 154089934281020522754315845)
            ·
              refine ⟨28891862677691348016434221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154089934281020522754315845 28891862677691348016434221)
              ·
                refine ⟨10834448504134255506162833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28891862677691348016434221 10834448504134255506162833)
                ·
                  refine ⟨8125836378100691629622125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10834448504134255506162833 8125836378100691629622125)
                  ·
                    refine ⟨3047188641787759361108297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8125836378100691629622125 3047188641787759361108297)
                    ·
                      refine ⟨2285391481340819520831223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047188641787759361108297 2285391481340819520831223)
                      ·
                        rfl

theorem cell23_4450784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_4450784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450784 prefixEnd_4450784 := by exact prefixLift 4450784
  have htrace : WordTrace (prefixWord ++ tailWord_4450784) baseStart_4450784 baseEnd_4450784 := by
    simpa [prefixWord, tailWord_4450784, baseEnd_4450784] using wordTrace_append hprefix tailTrace_4450784
  have hstable : (prefixWord ++ tailWord_4450784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450784).length < 2 ^ (prefixWord ++ tailWord_4450784).sum := by decide
  have hdescent : baseEnd_4450784 < baseStart_4450784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450794 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_4450794 : Nat := 118140960795 + 4450794 * 2 ^ 59
def prefixEnd_4450794 : Nat := 4983230072969 + 3 ^ 40 * 4450794 * 2
def baseEnd_4450794 : Nat := 761798872049121493902059

theorem tailTrace_4450794 : CollatzResearch.WordTrace tailWord_4450794 prefixEnd_4450794 761798872049121493902059 := by
  unfold tailWord_4450794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40583448359385236985715859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108222528958360631961908957 40583448359385236985715859)
  ·
    refine ⟨60875172539077855478573789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40583448359385236985715859 60875172539077855478573789)
    ·
      refine ⟨22828189702154195804465171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60875172539077855478573789 22828189702154195804465171)
      ·
        refine ⟨34242284553231293706697757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22828189702154195804465171 34242284553231293706697757)
        ·
          refine ⟨12840856707461735140011659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34242284553231293706697757 12840856707461735140011659)
          ·
            refine ⟨19261285061192602710017489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12840856707461735140011659 19261285061192602710017489)
            ·
              refine ⟨14445963795894452032513117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19261285061192602710017489 14445963795894452032513117)
              ·
                refine ⟨5417236423460419512192419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14445963795894452032513117 5417236423460419512192419)
                ·
                  refine ⟨8125854635190629268288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5417236423460419512192419 8125854635190629268288629)
                  ·
                    refine ⟨761798872049121493902059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8125854635190629268288629 761798872049121493902059)
                    ·
                      rfl

theorem cell23_4450794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_4450794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450794 prefixEnd_4450794 := by exact prefixLift 4450794
  have htrace : WordTrace (prefixWord ++ tailWord_4450794) baseStart_4450794 baseEnd_4450794 := by
    simpa [prefixWord, tailWord_4450794, baseEnd_4450794] using wordTrace_append hprefix tailTrace_4450794
  have hstable : (prefixWord ++ tailWord_4450794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450794).length < 2 ^ (prefixWord ++ tailWord_4450794).sum := by decide
  have hdescent : baseEnd_4450794 < baseStart_4450794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450808 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_4450808 : Nat := 118140960795 + 4450808 * 2 ^ 59
def prefixEnd_4450808 : Nat := 4983230072969 + 3 ^ 40 * 4450808 * 2
def baseEnd_4450808 : Nat := 2285403804876527426931113

theorem tailTrace_4450808 : CollatzResearch.WordTrace tailWord_4450808 prefixEnd_4450808 2285403804876527426931113 := by
  unfold tailWord_4450808
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167152029745114166936539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108222869372993485555915385 81167152029745114166936539)
  ·
    refine ⟨121750728044617671250404809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81167152029745114166936539 121750728044617671250404809)
    ·
      refine ⟨91313046033463253437803607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121750728044617671250404809 91313046033463253437803607)
      ·
        refine ⟨136969569050194880156705411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91313046033463253437803607 136969569050194880156705411)
        ·
          refine ⟨205454353575292320235058117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136969569050194880156705411 205454353575292320235058117)
          ·
            refine ⟨38522691295367310044073397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205454353575292320235058117 38522691295367310044073397)
            ·
              refine ⟨3611502308940685316631881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38522691295367310044073397 3611502308940685316631881)
              ·
                refine ⟨2708626731705513987473911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611502308940685316631881 2708626731705513987473911)
                ·
                  refine ⟨4062940097558270981210867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708626731705513987473911 4062940097558270981210867)
                  ·
                    refine ⟨6094410146337406471816301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062940097558270981210867 6094410146337406471816301)
                    ·
                      refine ⟨2285403804876527426931113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094410146337406471816301 2285403804876527426931113)
                      ·
                        rfl

theorem cell23_4450808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_4450808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450808 prefixEnd_4450808 := by exact prefixLift 4450808
  have htrace : WordTrace (prefixWord ++ tailWord_4450808) baseStart_4450808 baseEnd_4450808 := by
    simpa [prefixWord, tailWord_4450808, baseEnd_4450808] using wordTrace_append hprefix tailTrace_4450808
  have hstable : (prefixWord ++ tailWord_4450808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450808).length < 2 ^ (prefixWord ++ tailWord_4450808).sum := by decide
  have hdescent : baseEnd_4450808 < baseStart_4450808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450827 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_4450827 : Nat := 118140960795 + 4450827 * 2 ^ 59
def prefixEnd_4450827 : Nat := 4983230072969 + 3 ^ 40 * 4450827 * 2
def baseEnd_4450827 : Nat := 2285413561008962852593525

theorem tailTrace_4450827 : CollatzResearch.WordTrace tailWord_4450827 prefixEnd_4450827 2285413561008962852593525 := by
  unfold tailWord_4450827
  simp only [CollatzResearch.WordTrace]
  refine ⟨162334997046421394578814735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108223331364280929719209823 162334997046421394578814735)
  ·
    refine ⟨243502495569632091868222103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162334997046421394578814735 243502495569632091868222103)
    ·
      refine ⟨365253743354448137802333155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243502495569632091868222103 365253743354448137802333155)
      ·
        refine ⟨547880615031672206703499733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365253743354448137802333155 547880615031672206703499733)
        ·
          refine ⟨12840951914804817344613275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 547880615031672206703499733 12840951914804817344613275)
          ·
            refine ⟨19261427872207226016919913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12840951914804817344613275 19261427872207226016919913)
            ·
              refine ⟨14446070904155419512689935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19261427872207226016919913 14446070904155419512689935)
              ·
                refine ⟨21669106356233129269034903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14446070904155419512689935 21669106356233129269034903)
                ·
                  refine ⟨32503659534349693903552355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21669106356233129269034903 32503659534349693903552355)
                  ·
                    refine ⟨48755489301524540855328533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32503659534349693903552355 48755489301524540855328533)
                    ·
                      refine ⟨2285413561008962852593525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48755489301524540855328533 2285413561008962852593525)
                      ·
                        rfl

theorem cell23_4450827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_4450827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450827 prefixEnd_4450827 := by exact prefixLift 4450827
  have htrace : WordTrace (prefixWord ++ tailWord_4450827) baseStart_4450827 baseEnd_4450827 := by
    simpa [prefixWord, tailWord_4450827, baseEnd_4450827] using wordTrace_append hprefix tailTrace_4450827
  have hstable : (prefixWord ++ tailWord_4450827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450827).length < 2 ^ (prefixWord ++ tailWord_4450827).sum := by decide
  have hdescent : baseEnd_4450827 < baseStart_4450827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450844 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4450844 : Nat := 118140960795 + 4450844 * 2 ^ 59
def prefixEnd_4450844 : Nat := 4983230072969 + 3 ^ 40 * 4450844 * 2
def baseEnd_4450844 : Nat := 2285422290180089286080947

theorem tailTrace_4450844 : CollatzResearch.WordTrace tailWord_4450844 prefixEnd_4450844 2285422290180089286080947 := by
  unfold tailWord_4450844
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167808543679903241091793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108223744724906537654789057 81167808543679903241091793)
  ·
    refine ⟨60875856407759927430818845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81167808543679903241091793 60875856407759927430818845)
    ·
      refine ⟨22828446152909972786557067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60875856407759927430818845 22828446152909972786557067)
      ·
        refine ⟨34242669229364959179835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22828446152909972786557067 34242669229364959179835601)
        ·
          refine ⟨25682001922023719384876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34242669229364959179835601 25682001922023719384876701)
          ·
            refine ⟨9630750720758894769328763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25682001922023719384876701 9630750720758894769328763)
            ·
              refine ⟨14446126081138342153993145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9630750720758894769328763 14446126081138342153993145)
              ·
                refine ⟨10834594560853756615494859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14446126081138342153993145 10834594560853756615494859)
                ·
                  refine ⟨16251891841280634923242289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10834594560853756615494859 16251891841280634923242289)
                  ·
                    refine ⟨12188918880960476192431717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16251891841280634923242289 12188918880960476192431717)
                    ·
                      refine ⟨2285422290180089286080947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12188918880960476192431717 2285422290180089286080947)
                      ·
                        rfl

theorem cell23_4450844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4450844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450844 prefixEnd_4450844 := by exact prefixLift 4450844
  have htrace : WordTrace (prefixWord ++ tailWord_4450844) baseStart_4450844 baseEnd_4450844 := by
    simpa [prefixWord, tailWord_4450844, baseEnd_4450844] using wordTrace_append hprefix tailTrace_4450844
  have hstable : (prefixWord ++ tailWord_4450844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450844).length < 2 ^ (prefixWord ++ tailWord_4450844).sum := by decide
  have hdescent : baseEnd_4450844 < baseStart_4450844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450848 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4450848 : Nat := 118140960795 + 4450848 * 2 ^ 59
def prefixEnd_4450848 : Nat := 4983230072969 + 3 ^ 40 * 4450848 * 2
def baseEnd_4450848 : Nat := 2285424344102707270430929

theorem tailTrace_4450848 : CollatzResearch.WordTrace tailWord_4450848 prefixEnd_4450848 2285424344102707270430929 := by
  unfold tailWord_4450848
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167881489672657582664599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108223841986230210110219465 81167881489672657582664599)
  ·
    refine ⟨121751822234508986373996899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81167881489672657582664599 121751822234508986373996899)
    ·
      refine ⟨182627733351763479560995349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121751822234508986373996899 182627733351763479560995349)
      ·
        refine ⟨8560675000863913104421657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182627733351763479560995349 8560675000863913104421657)
        ·
          refine ⟨6420506250647934828316243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8560675000863913104421657 6420506250647934828316243)
          ·
            refine ⟨9630759375971902242474365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420506250647934828316243 9630759375971902242474365)
            ·
              refine ⟨3611534765989463340927887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9630759375971902242474365 3611534765989463340927887)
              ·
                refine ⟨5417302148984195011391831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611534765989463340927887 5417302148984195011391831)
                ·
                  refine ⟨8125953223476292517087747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5417302148984195011391831 8125953223476292517087747)
                  ·
                    refine ⟨12188929835214438775631621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8125953223476292517087747 12188929835214438775631621)
                    ·
                      refine ⟨2285424344102707270430929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12188929835214438775631621 2285424344102707270430929)
                      ·
                        rfl

theorem cell23_4450848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4450848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450848 prefixEnd_4450848 := by exact prefixLift 4450848
  have htrace : WordTrace (prefixWord ++ tailWord_4450848) baseStart_4450848 baseEnd_4450848 := by
    simpa [prefixWord, tailWord_4450848, baseEnd_4450848] using wordTrace_append hprefix tailTrace_4450848
  have hstable : (prefixWord ++ tailWord_4450848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450848).length < 2 ^ (prefixWord ++ tailWord_4450848).sum := by decide
  have hdescent : baseEnd_4450848 < baseStart_4450848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450864 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_4450864 : Nat := 118140960795 + 4450864 * 2 ^ 59
def prefixEnd_4450864 : Nat := 4983230072969 + 3 ^ 40 * 4450864 * 2
def baseEnd_4450864 : Nat := 2285432559793179207830855

theorem tailTrace_4450864 : CollatzResearch.WordTrace tailWord_4450864 prefixEnd_4450864 2285432559793179207830855 := by
  unfold tailWord_4450864
  simp only [CollatzResearch.WordTrace]
  refine ⟨81168173273643674948955823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108224231031524899931941097 81168173273643674948955823)
  ·
    refine ⟨121752259910465512423433735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81168173273643674948955823 121752259910465512423433735)
    ·
      refine ⟨182628389865698268635150603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121752259910465512423433735 182628389865698268635150603)
      ·
        refine ⟨273942584798547402952725905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182628389865698268635150603 273942584798547402952725905)
        ·
          refine ⟨205456938598910552214544429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273942584798547402952725905 205456938598910552214544429)
          ·
            refine ⟨77046351974591457080454161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205456938598910552214544429 77046351974591457080454161)
            ·
              refine ⟨57784763980943592810340621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77046351974591457080454161 57784763980943592810340621)
              ·
                refine ⟨21669286492853847303877733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57784763980943592810340621 21669286492853847303877733)
                ·
                  refine ⟨4062991217410096369477075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21669286492853847303877733 4062991217410096369477075)
                  ·
                    refine ⟨6094486826115144554215613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062991217410096369477075 6094486826115144554215613)
                    ·
                      refine ⟨2285432559793179207830855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094486826115144554215613 2285432559793179207830855)
                      ·
                        rfl

theorem cell23_4450864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_4450864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450864 prefixEnd_4450864 := by exact prefixLift 4450864
  have htrace : WordTrace (prefixWord ++ tailWord_4450864) baseStart_4450864 baseEnd_4450864 := by
    simpa [prefixWord, tailWord_4450864, baseEnd_4450864] using wordTrace_append hprefix tailTrace_4450864
  have hstable : (prefixWord ++ tailWord_4450864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450864).length < 2 ^ (prefixWord ++ tailWord_4450864).sum := by decide
  have hdescent : baseEnd_4450864 < baseStart_4450864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450865 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_4450865 : Nat := 118140960795 + 4450865 * 2 ^ 59
def prefixEnd_4450865 : Nat := 4983230072969 + 3 ^ 40 * 4450865 * 2
def baseEnd_4450865 : Nat := 2285433073273833703918351

theorem tailTrace_4450865 : CollatzResearch.WordTrace tailWord_4450865 prefixEnd_4450865 2285433073273833703918351 := by
  unfold tailWord_4450865
  simp only [CollatzResearch.WordTrace]
  refine ⟨162336383020283727068698049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108224255346855818045798699 162336383020283727068698049)
  ·
    refine ⟨121752287265212795301523537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162336383020283727068698049 121752287265212795301523537)
    ·
      refine ⟨91314215448909596476142653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121752287265212795301523537 91314215448909596476142653)
      ·
        refine ⟨34242830793341098678553495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91314215448909596476142653 34242830793341098678553495)
        ·
          refine ⟨51364246190011648017830243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34242830793341098678553495 51364246190011648017830243)
          ·
            refine ⟨77046369285017472026745365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51364246190011648017830243 77046369285017472026745365)
            ·
              refine ⟨3611548560235194001253689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77046369285017472026745365 3611548560235194001253689)
              ·
                refine ⟨2708661420176395500940267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611548560235194001253689 2708661420176395500940267)
                ·
                  refine ⟨4062992130264593251410401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708661420176395500940267 4062992130264593251410401)
                  ·
                    refine ⟨3047244097698444938557801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062992130264593251410401 3047244097698444938557801)
                    ·
                      refine ⟨2285433073273833703918351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047244097698444938557801 2285433073273833703918351)
                      ·
                        rfl

theorem cell23_4450865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_4450865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450865 prefixEnd_4450865 := by exact prefixLift 4450865
  have htrace : WordTrace (prefixWord ++ tailWord_4450865) baseStart_4450865 baseEnd_4450865 := by
    simpa [prefixWord, tailWord_4450865, baseEnd_4450865] using wordTrace_append hprefix tailTrace_4450865
  have hstable : (prefixWord ++ tailWord_4450865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450865).length < 2 ^ (prefixWord ++ tailWord_4450865).sum := by decide
  have hdescent : baseEnd_4450865 < baseStart_4450865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450878 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4450878 : Nat := 118140960795 + 4450878 * 2 ^ 59
def prefixEnd_4450878 : Nat := 4983230072969 + 3 ^ 40 * 4450878 * 2
def baseEnd_4450878 : Nat := 2285439748522342153055791

theorem tailTrace_4450878 : CollatzResearch.WordTrace tailWord_4450878 prefixEnd_4450878 2285439748522342153055791 := by
  unfold tailWord_4450878
  simp only [CollatzResearch.WordTrace]
  refine ⟨20292107146154578786115161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108224571446157753525947525 20292107146154578786115161)
  ·
    refine ⟨15219080359615934089586371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20292107146154578786115161 15219080359615934089586371)
    ·
      refine ⟨22828620539423901134379557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15219080359615934089586371 22828620539423901134379557)
      ·
        refine ⟨4280366351141981462696167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22828620539423901134379557 4280366351141981462696167)
        ·
          refine ⟨6420549526712972194044251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280366351141981462696167 6420549526712972194044251)
          ·
            refine ⟨9630824290069458291066377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420549526712972194044251 9630824290069458291066377)
            ·
              refine ⟨7223118217552093718299783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9630824290069458291066377 7223118217552093718299783)
              ·
                refine ⟨10834677326328140577449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223118217552093718299783 10834677326328140577449675)
                ·
                  refine ⟨16252015989492210866174513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10834677326328140577449675 16252015989492210866174513)
                  ·
                    refine ⟨12189011992119158149630885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16252015989492210866174513 12189011992119158149630885)
                    ·
                      refine ⟨2285439748522342153055791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12189011992119158149630885 2285439748522342153055791)
                      ·
                        rfl

theorem cell23_4450878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4450878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450878 prefixEnd_4450878 := by exact prefixLift 4450878
  have htrace : WordTrace (prefixWord ++ tailWord_4450878) baseStart_4450878 baseEnd_4450878 := by
    simpa [prefixWord, tailWord_4450878, baseEnd_4450878] using wordTrace_append hprefix tailTrace_4450878
  have hstable : (prefixWord ++ tailWord_4450878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450878).length < 2 ^ (prefixWord ++ tailWord_4450878).sum := by decide
  have hdescent : baseEnd_4450878 < baseStart_4450878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450881 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4450881 : Nat := 118140960795 + 4450881 * 2 ^ 59
def prefixEnd_4450881 : Nat := 4983230072969 + 3 ^ 40 * 4450881 * 2
def baseEnd_4450881 : Nat := 2285441288964305641318277

theorem tailTrace_4450881 : CollatzResearch.WordTrace tailWord_4450881 prefixEnd_4450881 2285441288964305641318277 := by
  unfold tailWord_4450881
  simp only [CollatzResearch.WordTrace]
  refine ⟨162336966588225761801280497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108224644392150507867520331 162336966588225761801280497)
  ·
    refine ⟨121752724941169321350960373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162336966588225761801280497 121752724941169321350960373)
    ·
      refine ⟨11414317963234623876652535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121752724941169321350960373 11414317963234623876652535)
      ·
        refine ⟨17121476944851935814978803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11414317963234623876652535 17121476944851935814978803)
        ·
          refine ⟨25682215417277903722468205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17121476944851935814978803 25682215417277903722468205)
          ·
            refine ⟨9630830781479213895925577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25682215417277903722468205 9630830781479213895925577)
            ·
              refine ⟨7223123086109410421944183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9630830781479213895925577 7223123086109410421944183)
              ·
                refine ⟨10834684629164115632916275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223123086109410421944183 10834684629164115632916275)
                ·
                  refine ⟨16252026943746173449374413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10834684629164115632916275 16252026943746173449374413)
                  ·
                    refine ⟨6094510103904815043515405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16252026943746173449374413 6094510103904815043515405)
                    ·
                      refine ⟨2285441288964305641318277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094510103904815043515405 2285441288964305641318277)
                      ·
                        rfl

theorem cell23_4450881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4450881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450881 prefixEnd_4450881 := by exact prefixLift 4450881
  have htrace : WordTrace (prefixWord ++ tailWord_4450881) baseStart_4450881 baseEnd_4450881 := by
    simpa [prefixWord, tailWord_4450881, baseEnd_4450881] using wordTrace_append hprefix tailTrace_4450881
  have hstable : (prefixWord ++ tailWord_4450881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450881).length < 2 ^ (prefixWord ++ tailWord_4450881).sum := by decide
  have hdescent : baseEnd_4450881 < baseStart_4450881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450927 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 7]
def baseStart_4450927 : Nat := 118140960795 + 4450927 * 2 ^ 59
def prefixEnd_4450927 : Nat := 4983230072969 + 3 ^ 40 * 4450927 * 2
def baseEnd_4450927 : Nat := 253940545452712495704785

theorem tailTrace_4450927 : CollatzResearch.WordTrace tailWord_4450927 prefixEnd_4450927 253940545452712495704785 := by
  unfold tailWord_4450927
  simp only [CollatzResearch.WordTrace]
  refine ⟨162338644346059111657455035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108225762897372741104970023 162338644346059111657455035)
  ·
    refine ⟨243507966519088667486182553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162338644346059111657455035 243507966519088667486182553)
    ·
      refine ⟨182630974889316500614636915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243507966519088667486182553 182630974889316500614636915)
      ·
        refine ⟨273946462333974750921955373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182630974889316500614636915 273946462333974750921955373)
        ·
          refine ⟨102729923375240531595733265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273946462333974750921955373 102729923375240531595733265)
          ·
            refine ⟨77047442531430398696799949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102729923375240531595733265 77047442531430398696799949)
            ·
              refine ⟨28892790949286399511299981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77047442531430398696799949 28892790949286399511299981)
              ·
                refine ⟨10834796605982399816737493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28892790949286399511299981 10834796605982399816737493)
                ·
                  refine ⟨253940545452712495704785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10834796605982399816737493 253940545452712495704785)
                  ·
                    rfl

theorem cell23_4450927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 7].length) (baseStart_4450927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450927 prefixEnd_4450927 := by exact prefixLift 4450927
  have htrace : WordTrace (prefixWord ++ tailWord_4450927) baseStart_4450927 baseEnd_4450927 := by
    simpa [prefixWord, tailWord_4450927, baseEnd_4450927] using wordTrace_append hprefix tailTrace_4450927
  have hstable : (prefixWord ++ tailWord_4450927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450927).length < 2 ^ (prefixWord ++ tailWord_4450927).sum := by decide
  have hdescent : baseEnd_4450927 < baseStart_4450927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450994 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4450994 : Nat := 118140960795 + 4450994 * 2 ^ 59
def prefixEnd_4450994 : Nat := 4983230072969 + 3 ^ 40 * 4450994 * 2
def baseEnd_4450994 : Nat := 2285499312278263699205257

theorem tailTrace_4450994 : CollatzResearch.WordTrace tailWord_4450994 prefixEnd_4450994 2285499312278263699205257 := by
  unfold tailWord_4450994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40585272009204095525036009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108227392024544254733429357 40585272009204095525036009)
  ·
    refine ⟨30438954006903071643777007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40585272009204095525036009 30438954006903071643777007)
    ·
      refine ⟨45658431010354607465665511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30438954006903071643777007 45658431010354607465665511)
      ·
        refine ⟨68487646515531911198498267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45658431010354607465665511 68487646515531911198498267)
        ·
          refine ⟨102731469773297866797747401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68487646515531911198498267 102731469773297866797747401)
          ·
            refine ⟨77048602329973400098310551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102731469773297866797747401 77048602329973400098310551)
            ·
              refine ⟨115572903494960100147465827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77048602329973400098310551 115572903494960100147465827)
              ·
                refine ⟨173359355242440150221198741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115572903494960100147465827 173359355242440150221198741)
                ·
                  refine ⟨8126219776989382041618691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 173359355242440150221198741 8126219776989382041618691)
                  ·
                    refine ⟨12189329665484073062428037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8126219776989382041618691 12189329665484073062428037)
                    ·
                      refine ⟨2285499312278263699205257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12189329665484073062428037 2285499312278263699205257)
                      ·
                        rfl

theorem cell23_4450994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4450994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450994 prefixEnd_4450994 := by exact prefixLift 4450994
  have htrace : WordTrace (prefixWord ++ tailWord_4450994) baseStart_4450994 baseEnd_4450994 := by
    simpa [prefixWord, tailWord_4450994, baseEnd_4450994] using wordTrace_append hprefix tailTrace_4450994
  have hstable : (prefixWord ++ tailWord_4450994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450994).length < 2 ^ (prefixWord ++ tailWord_4450994).sum := by decide
  have hdescent : baseEnd_4450994 < baseStart_4450994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451027 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_4451027 : Nat := 118140960795 + 4451027 * 2 ^ 59
def prefixEnd_4451027 : Nat := 4983230072969 + 3 ^ 40 * 4451027 * 2
def baseEnd_4451027 : Nat := 2285516257139862070092605

theorem tailTrace_4451027 : CollatzResearch.WordTrace tailWord_4451027 prefixEnd_4451027 2285516257139862070092605 := by
  unfold tailWord_4451027
  simp only [CollatzResearch.WordTrace]
  refine ⟨162342291645696828736095335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108228194430464552490730223 162342291645696828736095335)
  ·
    refine ⟨243513437468545243104143003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162342291645696828736095335 243513437468545243104143003)
    ·
      refine ⟨365270156202817864656214505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243513437468545243104143003 365270156202817864656214505)
      ·
        refine ⟨273952617152113398492160879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365270156202817864656214505 273952617152113398492160879)
        ·
          refine ⟨410928925728170097738241319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273952617152113398492160879 410928925728170097738241319)
          ·
            refine ⟨616393388592255146607361979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410928925728170097738241319 616393388592255146607361979)
            ·
              refine ⟨924590082888382719911042969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616393388592255146607361979 924590082888382719911042969)
              ·
                refine ⟨693442562166287039933282227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924590082888382719911042969 693442562166287039933282227)
                ·
                  refine ⟨1040163843249430559899923341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693442562166287039933282227 1040163843249430559899923341)
                  ·
                    refine ⟨390061441218536459962471253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040163843249430559899923341 390061441218536459962471253)
                    ·
                      refine ⟨2285516257139862070092605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 390061441218536459962471253 2285516257139862070092605)
                      ·
                        rfl

theorem cell23_4451027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_4451027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451027 prefixEnd_4451027 := by exact prefixLift 4451027
  have htrace : WordTrace (prefixWord ++ tailWord_4451027) baseStart_4451027 baseEnd_4451027 := by
    simpa [prefixWord, tailWord_4451027, baseEnd_4451027] using wordTrace_append hprefix tailTrace_4451027
  have hstable : (prefixWord ++ tailWord_4451027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451027).length < 2 ^ (prefixWord ++ tailWord_4451027).sum := by decide
  have hdescent : baseEnd_4451027 < baseStart_4451027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451031 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_4451031 : Nat := 118140960795 + 4451031 * 2 ^ 59
def prefixEnd_4451031 : Nat := 4983230072969 + 3 ^ 40 * 4451031 * 2
def baseEnd_4451031 : Nat := 2285518311062480054442587

theorem tailTrace_4451031 : CollatzResearch.WordTrace tailWord_4451031 prefixEnd_4451031 2285518311062480054442587 := by
  unfold tailWord_4451031
  simp only [CollatzResearch.WordTrace]
  refine ⟨162342437537682337419240947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108228291691788224946160631 162342437537682337419240947)
  ·
    refine ⟨243513656306523506128861421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162342437537682337419240947 243513656306523506128861421)
    ·
      refine ⟨91317621114946314798323033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243513656306523506128861421 91317621114946314798323033)
      ·
        refine ⟨68488215836209736098742275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91317621114946314798323033 68488215836209736098742275)
        ·
          refine ⟨102732323754314604148113413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68488215836209736098742275 102732323754314604148113413)
          ·
            refine ⟨19262310703933988277771265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102732323754314604148113413 19262310703933988277771265)
            ·
              refine ⟨14446733027950491208328449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19262310703933988277771265 14446733027950491208328449)
              ·
                refine ⟨10835049770962868406246337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14446733027950491208328449 10835049770962868406246337)
                ·
                  refine ⟨8126287328222151304684753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10835049770962868406246337 8126287328222151304684753)
                  ·
                    refine ⟨6094715496166613478513565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8126287328222151304684753 6094715496166613478513565)
                    ·
                      refine ⟨2285518311062480054442587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094715496166613478513565 2285518311062480054442587)
                      ·
                        rfl

theorem cell23_4451031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_4451031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451031 prefixEnd_4451031 := by exact prefixLift 4451031
  have htrace : WordTrace (prefixWord ++ tailWord_4451031) baseStart_4451031 baseEnd_4451031 := by
    simpa [prefixWord, tailWord_4451031, baseEnd_4451031] using wordTrace_append hprefix tailTrace_4451031
  have hstable : (prefixWord ++ tailWord_4451031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451031).length < 2 ^ (prefixWord ++ tailWord_4451031).sum := by decide
  have hdescent : baseEnd_4451031 < baseStart_4451031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451064 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_4451064 : Nat := 118140960795 + 4451064 * 2 ^ 59
def prefixEnd_4451064 : Nat := 4983230072969 + 3 ^ 40 * 4451064 * 2
def baseEnd_4451064 : Nat := 761845085308026141776645

theorem tailTrace_4451064 : CollatzResearch.WordTrace tailWord_4451064 prefixEnd_4451064 761845085308026141776645 := by
  unfold tailWord_4451064
  simp only [CollatzResearch.WordTrace]
  refine ⟨81171820573281392027596123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108229094097708522703461497 81171820573281392027596123)
  ·
    refine ⟨121757730859922088041394185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81171820573281392027596123 121757730859922088041394185)
    ·
      refine ⟨91318298144941566031045639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121757730859922088041394185 91318298144941566031045639)
      ·
        refine ⟨136977447217412349046568459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91318298144941566031045639 136977447217412349046568459)
        ·
          refine ⟨205466170826118523569852689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136977447217412349046568459 205466170826118523569852689)
          ·
            refine ⟨154099628119588892677389517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205466170826118523569852689 154099628119588892677389517)
            ·
              refine ⟨57787360544845834754021069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154099628119588892677389517 57787360544845834754021069)
              ·
                refine ⟨21670260204317188032757901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57787360544845834754021069 21670260204317188032757901)
                ·
                  refine ⟨8126347576618945512284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21670260204317188032757901 8126347576618945512284213)
                  ·
                    refine ⟨761845085308026141776645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8126347576618945512284213 761845085308026141776645)
                    ·
                      rfl

theorem cell23_4451064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_4451064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451064 prefixEnd_4451064 := by exact prefixLift 4451064
  have htrace : WordTrace (prefixWord ++ tailWord_4451064) baseStart_4451064 baseEnd_4451064 := by
    simpa [prefixWord, tailWord_4451064, baseEnd_4451064] using wordTrace_append hprefix tailTrace_4451064
  have hstable : (prefixWord ++ tailWord_4451064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451064).length < 2 ^ (prefixWord ++ tailWord_4451064).sum := by decide
  have hdescent : baseEnd_4451064 < baseStart_4451064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451095 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4451095 : Nat := 118140960795 + 4451095 * 2 ^ 59
def prefixEnd_4451095 : Nat := 4983230072969 + 3 ^ 40 * 4451095 * 2
def baseEnd_4451095 : Nat := 2285551173824367804042293

theorem tailTrace_4451095 : CollatzResearch.WordTrace tailWord_4451095 prefixEnd_4451095 2285551173824367804042293 := by
  unfold tailWord_4451095
  simp only [CollatzResearch.WordTrace]
  refine ⟨162344771809450476349570739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108229847872966984233047159 162344771809450476349570739)
  ·
    refine ⟨243517157714175714524356109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162344771809450476349570739 243517157714175714524356109)
    ·
      refine ⟨91318934142815892946633541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243517157714175714524356109 91318934142815892946633541)
      ·
        refine ⟨17122300151777979927493789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91318934142815892946633541 17122300151777979927493789)
        ·
          refine ⟨6420862556916742472810171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17122300151777979927493789 6420862556916742472810171)
          ·
            refine ⟨9631293835375113709215257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420862556916742472810171 9631293835375113709215257)
            ·
              refine ⟨7223470376531335281911443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9631293835375113709215257 7223470376531335281911443)
              ·
                refine ⟨10835205564797002922867165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223470376531335281911443 10835205564797002922867165)
                ·
                  refine ⟨4063202086798876096075187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10835205564797002922867165 4063202086798876096075187)
                  ·
                    refine ⟨6094803130198314144112781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063202086798876096075187 6094803130198314144112781)
                    ·
                      refine ⟨2285551173824367804042293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094803130198314144112781 2285551173824367804042293)
                      ·
                        rfl

theorem cell23_4451095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4451095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451095 prefixEnd_4451095 := by exact prefixLift 4451095
  have htrace : WordTrace (prefixWord ++ tailWord_4451095) baseStart_4451095 baseEnd_4451095 := by
    simpa [prefixWord, tailWord_4451095, baseEnd_4451095] using wordTrace_append hprefix tailTrace_4451095
  have hstable : (prefixWord ++ tailWord_4451095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451095).length < 2 ^ (prefixWord ++ tailWord_4451095).sum := by decide
  have hdescent : baseEnd_4451095 < baseStart_4451095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451211 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3]
def baseStart_4451211 : Nat := 118140960795 + 4451211 * 2 ^ 59
def prefixEnd_4451211 : Nat := 4983230072969 + 3 ^ 40 * 4451211 * 2
def baseEnd_4451211 : Nat := 2285610737580289350191759

theorem tailTrace_4451211 : CollatzResearch.WordTrace tailWord_4451211 prefixEnd_4451211 2285610737580289350191759 := by
  unfold tailWord_4451211
  simp only [CollatzResearch.WordTrace]
  refine ⟨162349002677030228160793487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108232668451353485440528991 162349002677030228160793487)
  ·
    refine ⟨243523504015545342241190231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162349002677030228160793487 243523504015545342241190231)
    ·
      refine ⟨365285256023318013361785347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243523504015545342241190231 365285256023318013361785347)
      ·
        refine ⟨547927884034977020042678021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365285256023318013361785347 547927884034977020042678021)
        ·
          refine ⟨102736478256558191258002129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 547927884034977020042678021 102736478256558191258002129)
          ·
            refine ⟨77052358692418643443501597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102736478256558191258002129 77052358692418643443501597)
            ·
              refine ⟨28894634509656991291313099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77052358692418643443501597 28894634509656991291313099)
              ·
                refine ⟨43341951764485486936969649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28894634509656991291313099 43341951764485486936969649)
                ·
                  refine ⟨32506463823364115202727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43341951764485486936969649 32506463823364115202727237)
                  ·
                    refine ⟨6094961966880771600511357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32506463823364115202727237 6094961966880771600511357)
                    ·
                      refine ⟨2285610737580289350191759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6094961966880771600511357 2285610737580289350191759)
                      ·
                        rfl

theorem cell23_4451211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].length) (baseStart_4451211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451211 prefixEnd_4451211 := by exact prefixLift 4451211
  have htrace : WordTrace (prefixWord ++ tailWord_4451211) baseStart_4451211 baseEnd_4451211 := by
    simpa [prefixWord, tailWord_4451211, baseEnd_4451211] using wordTrace_append hprefix tailTrace_4451211
  have hstable : (prefixWord ++ tailWord_4451211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451211).length < 2 ^ (prefixWord ++ tailWord_4451211).sum := by decide
  have hdescent : baseEnd_4451211 < baseStart_4451211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451221 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4451221 : Nat := 118140960795 + 4451221 * 2 ^ 59
def prefixEnd_4451221 : Nat := 4983230072969 + 3 ^ 40 * 4451221 * 2
def baseEnd_4451221 : Nat := 2285615872386834311066713

theorem tailTrace_4451221 : CollatzResearch.WordTrace tailWord_4451221 prefixEnd_4451221 2285615872386834311066713 := by
  unfold tailWord_4451221
  simp only [CollatzResearch.WordTrace]
  refine ⟨162349367406993999868657517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108232911604662666579105011 162349367406993999868657517)
  ·
    refine ⟨60881012777622749950746569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162349367406993999868657517 60881012777622749950746569)
    ·
      refine ⟨45660759583217062463059927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60881012777622749950746569 45660759583217062463059927)
      ·
        refine ⟨68491139374825593694589891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45660759583217062463059927 68491139374825593694589891)
        ·
          refine ⟨102736709062238390541884837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68491139374825593694589891 102736709062238390541884837)
          ·
            refine ⟨19263132949169698226603407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102736709062238390541884837 19263132949169698226603407)
            ·
              refine ⟨28894699423754547339905111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19263132949169698226603407 28894699423754547339905111)
              ·
                refine ⟨43342049135631821009857667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28894699423754547339905111 43342049135631821009857667)
                ·
                  refine ⟨65013073703447731514786501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43342049135631821009857667 65013073703447731514786501)
                  ·
                    refine ⟨12189951319396449659022469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65013073703447731514786501 12189951319396449659022469)
                    ·
                      refine ⟨2285615872386834311066713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12189951319396449659022469 2285615872386834311066713)
                      ·
                        rfl

theorem cell23_4451221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4451221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451221 prefixEnd_4451221 := by exact prefixLift 4451221
  have htrace : WordTrace (prefixWord ++ tailWord_4451221) baseStart_4451221 baseEnd_4451221 := by
    simpa [prefixWord, tailWord_4451221, baseEnd_4451221] using wordTrace_append hprefix tailTrace_4451221
  have hstable : (prefixWord ++ tailWord_4451221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451221).length < 2 ^ (prefixWord ++ tailWord_4451221).sum := by decide
  have hdescent : baseEnd_4451221 < baseStart_4451221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451231 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 9]
def baseStart_4451231 : Nat := 118140960795 + 4451231 * 2 ^ 59
def prefixEnd_4451231 : Nat := 4983230072969 + 3 ^ 40 * 4451231 * 2
def baseEnd_4451231 : Nat := 253957889688153252437963

theorem tailTrace_4451231 : CollatzResearch.WordTrace tailWord_4451231 prefixEnd_4451231 253957889688153252437963 := by
  unfold tailWord_4451231
  simp only [CollatzResearch.WordTrace]
  refine ⟨162349732136957771576521547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108233154757971847717681031 162349732136957771576521547)
  ·
    refine ⟨243524598205436657364782321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162349732136957771576521547 243524598205436657364782321)
    ·
      refine ⟨182643448654077493023586741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243524598205436657364782321 182643448654077493023586741)
      ·
        refine ⟨17122823311319764970961257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182643448654077493023586741 17122823311319764970961257)
        ·
          refine ⟨12842117483489823728220943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17122823311319764970961257 12842117483489823728220943)
          ·
            refine ⟨19263176225234735592331415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12842117483489823728220943 19263176225234735592331415)
            ·
              refine ⟨28894764337852103388497123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19263176225234735592331415 28894764337852103388497123)
              ·
                refine ⟨43342146506778155082745685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28894764337852103388497123 43342146506778155082745685)
                ·
                  refine ⟨253957889688153252437963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43342146506778155082745685 253957889688153252437963)
                  ·
                    rfl

theorem cell23_4451231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 9].length) (baseStart_4451231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451231 prefixEnd_4451231 := by exact prefixLift 4451231
  have htrace : WordTrace (prefixWord ++ tailWord_4451231) baseStart_4451231 baseEnd_4451231 := by
    simpa [prefixWord, tailWord_4451231, baseEnd_4451231] using wordTrace_append hprefix tailTrace_4451231
  have hstable : (prefixWord ++ tailWord_4451231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451231).length < 2 ^ (prefixWord ++ tailWord_4451231).sum := by decide
  have hdescent : baseEnd_4451231 < baseStart_4451231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451241 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_4451241 : Nat := 118140960795 + 4451241 * 2 ^ 59
def prefixEnd_4451241 : Nat := 4983230072969 + 3 ^ 40 * 4451241 * 2
def baseEnd_4451241 : Nat := 2285626141999924232816621

theorem tailTrace_4451241 : CollatzResearch.WordTrace tailWord_4451241 prefixEnd_4451241 2285626141999924232816621 := by
  unfold tailWord_4451241
  simp only [CollatzResearch.WordTrace]
  refine ⟨162350096866921543284385577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108233397911281028856257051 162350096866921543284385577)
  ·
    refine ⟨121762572650191157463289183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162350096866921543284385577 121762572650191157463289183)
    ·
      refine ⟨182643858975286736194933775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121762572650191157463289183 182643858975286736194933775)
      ·
        refine ⟨273965788462930104292400663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182643858975286736194933775 273965788462930104292400663)
        ·
          refine ⟨410948682694395156438600995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273965788462930104292400663 410948682694395156438600995)
          ·
            refine ⟨616423024041592734657901493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410948682694395156438600995 616423024041592734657901493)
            ·
              refine ⟨57789658503899318874178265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 616423024041592734657901493 57789658503899318874178265)
              ·
                refine ⟨43342243877924489155633699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57789658503899318874178265 43342243877924489155633699)
                ·
                  refine ⟨65013365816886733733450549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43342243877924489155633699 65013365816886733733450549)
                  ·
                    refine ⟨6095003045333131287510989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65013365816886733733450549 6095003045333131287510989)
                    ·
                      refine ⟨2285626141999924232816621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095003045333131287510989 2285626141999924232816621)
                      ·
                        rfl

theorem cell23_4451241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_4451241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451241 prefixEnd_4451241 := by exact prefixLift 4451241
  have htrace : WordTrace (prefixWord ++ tailWord_4451241) baseStart_4451241 baseEnd_4451241 := by
    simpa [prefixWord, tailWord_4451241, baseEnd_4451241] using wordTrace_append hprefix tailTrace_4451241
  have hstable : (prefixWord ++ tailWord_4451241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451241).length < 2 ^ (prefixWord ++ tailWord_4451241).sum := by decide
  have hdescent : baseEnd_4451241 < baseStart_4451241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451270 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4451270 : Nat := 118140960795 + 4451270 * 2 ^ 59
def prefixEnd_4451270 : Nat := 4983230072969 + 3 ^ 40 * 4451270 * 2
def baseEnd_4451270 : Nat := 2285641032938904619353989

theorem tailTrace_4451270 : CollatzResearch.WordTrace tailWord_4451270 prefixEnd_4451270 2285641032938904619353989 := by
  unfold tailWord_4451270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073473580744265038662227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108234103055877654158127509 5073473580744265038662227)
  ·
    refine ⟨7610210371116397557993341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5073473580744265038662227 7610210371116397557993341)
    ·
      refine ⟨2853828889168649084247503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7610210371116397557993341 2853828889168649084247503)
      ·
        refine ⟨4280743333752973626371255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853828889168649084247503 4280743333752973626371255)
        ·
          refine ⟨6421115000629460439556883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280743333752973626371255 6421115000629460439556883)
          ·
            refine ⟨9631672500944190659335325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421115000629460439556883 9631672500944190659335325)
            ·
              refine ⟨3611877187854071497250747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9631672500944190659335325 3611877187854071497250747)
              ·
                refine ⟨5417815781781107245876121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611877187854071497250747 5417815781781107245876121)
                ·
                  refine ⟨4063361836335830434407091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5417815781781107245876121 4063361836335830434407091)
                  ·
                    refine ⟨6095042754503745651610637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063361836335830434407091 6095042754503745651610637)
                    ·
                      refine ⟨2285641032938904619353989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095042754503745651610637 2285641032938904619353989)
                      ·
                        rfl

theorem cell23_4451270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4451270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451270 prefixEnd_4451270 := by exact prefixLift 4451270
  have htrace : WordTrace (prefixWord ++ tailWord_4451270) baseStart_4451270 baseEnd_4451270 := by
    simpa [prefixWord, tailWord_4451270, baseEnd_4451270] using wordTrace_append hprefix tailTrace_4451270
  have hstable : (prefixWord ++ tailWord_4451270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451270).length < 2 ^ (prefixWord ++ tailWord_4451270).sum := by decide
  have hdescent : baseEnd_4451270 < baseStart_4451270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451271 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4451271 : Nat := 118140960795 + 4451271 * 2 ^ 59
def prefixEnd_4451271 : Nat := 4983230072969 + 3 ^ 40 * 4451271 * 2
def baseEnd_4451271 : Nat := 2285641546419559115441483

theorem tailTrace_4451271 : CollatzResearch.WordTrace tailWord_4451271 prefixEnd_4451271 2285641546419559115441483 := by
  unfold tailWord_4451271
  simp only [CollatzResearch.WordTrace]
  refine ⟨162351191056812858407977667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108234127371208572271985111 162351191056812858407977667)
  ·
    refine ⟨243526786585219287611966501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162351191056812858407977667 243526786585219287611966501)
    ·
      refine ⟨45661272484728616427243719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243526786585219287611966501 45661272484728616427243719)
      ·
        refine ⟨68491908727092924640865579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45661272484728616427243719 68491908727092924640865579)
        ·
          refine ⟨102737863090639386961298369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68491908727092924640865579 102737863090639386961298369)
          ·
            refine ⟨77053397317979540220973777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102737863090639386961298369 77053397317979540220973777)
            ·
              refine ⟨57790047988484655165730333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77053397317979540220973777 57790047988484655165730333)
              ·
                refine ⟨21671267995681745687148875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57790047988484655165730333 21671267995681745687148875)
                ·
                  refine ⟨32506901993522618530723313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21671267995681745687148875 32506901993522618530723313)
                  ·
                    refine ⟨24380176495141963898042485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32506901993522618530723313 24380176495141963898042485)
                    ·
                      refine ⟨2285641546419559115441483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24380176495141963898042485 2285641546419559115441483)
                      ·
                        rfl

theorem cell23_4451271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4451271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451271 prefixEnd_4451271 := by exact prefixLift 4451271
  have htrace : WordTrace (prefixWord ++ tailWord_4451271) baseStart_4451271 baseEnd_4451271 := by
    simpa [prefixWord, tailWord_4451271, baseEnd_4451271] using wordTrace_append hprefix tailTrace_4451271
  have hstable : (prefixWord ++ tailWord_4451271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451271).length < 2 ^ (prefixWord ++ tailWord_4451271).sum := by decide
  have hdescent : baseEnd_4451271 < baseStart_4451271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451281 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_4451281 : Nat := 118140960795 + 4451281 * 2 ^ 59
def prefixEnd_4451281 : Nat := 4983230072969 + 3 ^ 40 * 4451281 * 2
def baseEnd_4451281 : Nat := 2285646681226104076316437

theorem tailTrace_4451281 : CollatzResearch.WordTrace tailWord_4451281 prefixEnd_4451281 2285646681226104076316437 := by
  unfold tailWord_4451281
  simp only [CollatzResearch.WordTrace]
  refine ⟨162351555786776630115841697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108234370524517753410561131 162351555786776630115841697)
  ·
    refine ⟨121763666840082472586881273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162351555786776630115841697 121763666840082472586881273)
    ·
      refine ⟨91322750130061854440160955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121763666840082472586881273 91322750130061854440160955)
      ·
        refine ⟨136984125195092781660241433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91322750130061854440160955 136984125195092781660241433)
        ·
          refine ⟨102738093896319586245181075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136984125195092781660241433 102738093896319586245181075)
          ·
            refine ⟨154107140844479379367771613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102738093896319586245181075 154107140844479379367771613)
            ·
              refine ⟨57790177816679767262914355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154107140844479379367771613 57790177816679767262914355)
              ·
                refine ⟨86685266725019650894371533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57790177816679767262914355 86685266725019650894371533)
                ·
                  refine ⟨32506975021882369085389325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86685266725019650894371533 32506975021882369085389325)
                  ·
                    refine ⟨12190115633205888407020997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32506975021882369085389325 12190115633205888407020997)
                    ·
                      refine ⟨2285646681226104076316437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12190115633205888407020997 2285646681226104076316437)
                      ·
                        rfl

theorem cell23_4451281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_4451281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451281 prefixEnd_4451281 := by exact prefixLift 4451281
  have htrace : WordTrace (prefixWord ++ tailWord_4451281) baseStart_4451281 baseEnd_4451281 := by
    simpa [prefixWord, tailWord_4451281, baseEnd_4451281] using wordTrace_append hprefix tailTrace_4451281
  have hstable : (prefixWord ++ tailWord_4451281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451281).length < 2 ^ (prefixWord ++ tailWord_4451281).sum := by decide
  have hdescent : baseEnd_4451281 < baseStart_4451281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451316 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4451316 : Nat := 118140960795 + 4451316 * 2 ^ 59
def prefixEnd_4451316 : Nat := 4983230072969 + 3 ^ 40 * 4451316 * 2
def baseEnd_4451316 : Nat := 253962739227667937708753

theorem tailTrace_4451316 : CollatzResearch.WordTrace tailWord_4451316 prefixEnd_4451316 253962739227667937708753 := by
  unfold tailWord_4451316
  simp only [CollatzResearch.WordTrace]
  refine ⟨81176416170824915546682901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108235221561099887395577201 81176416170824915546682901)
  ·
    refine ⟨3805144508007417916250761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81176416170824915546682901 3805144508007417916250761)
    ·
      refine ⟨2853858381005563437188071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805144508007417916250761 2853858381005563437188071)
      ·
        refine ⟨4280787571508345155782107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853858381005563437188071 4280787571508345155782107)
        ·
          refine ⟨6421181357262517733673161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280787571508345155782107 6421181357262517733673161)
          ·
            refine ⟨4815886017946888300254871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6421181357262517733673161 4815886017946888300254871)
            ·
              refine ⟨7223829026920332450382307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815886017946888300254871 7223829026920332450382307)
              ·
                refine ⟨10835743540380498675573461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223829026920332450382307 10835743540380498675573461)
                ·
                  refine ⟨253962739227667937708753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10835743540380498675573461 253962739227667937708753)
                  ·
                    rfl

theorem cell23_4451316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4451316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451316 prefixEnd_4451316 := by exact prefixLift 4451316
  have htrace : WordTrace (prefixWord ++ tailWord_4451316) baseStart_4451316 baseEnd_4451316 := by
    simpa [prefixWord, tailWord_4451316, baseEnd_4451316] using wordTrace_append hprefix tailTrace_4451316
  have hstable : (prefixWord ++ tailWord_4451316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451316).length < 2 ^ (prefixWord ++ tailWord_4451316).sum := by decide
  have hdescent : baseEnd_4451316 < baseStart_4451316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451321 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 8]
def baseStart_4451321 : Nat := 118140960795 + 4451321 * 2 ^ 59
def prefixEnd_4451321 : Nat := 4983230072969 + 3 ^ 40 * 4451321 * 2
def baseEnd_4451321 : Nat := 253963024494698213312917

theorem tailTrace_4451321 : CollatzResearch.WordTrace tailWord_4451321 prefixEnd_4451321 253963024494698213312917 := by
  unfold tailWord_4451321
  simp only [CollatzResearch.WordTrace]
  refine ⟨162353014706631716947297817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108235343137754477964865211 162353014706631716947297817)
  ·
    refine ⟨121764761029973787710473363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162353014706631716947297817 121764761029973787710473363)
    ·
      refine ⟨182647141544960681565710045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121764761029973787710473363 182647141544960681565710045)
      ·
        refine ⟨68492678079360255587141267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182647141544960681565710045 68492678079360255587141267)
        ·
          refine ⟨102739017119040383380711901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68492678079360255587141267 102739017119040383380711901)
          ·
            refine ⟨38527131419640143767766963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102739017119040383380711901 38527131419640143767766963)
            ·
              refine ⟨57790697129460215651650445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38527131419640143767766963 57790697129460215651650445)
              ·
                refine ⟨21671511423547580869368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57790697129460215651650445 21671511423547580869368917)
                ·
                  refine ⟨253963024494698213312917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21671511423547580869368917 253963024494698213312917)
                  ·
                    rfl

theorem cell23_4451321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_4451321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451321 prefixEnd_4451321 := by exact prefixLift 4451321
  have htrace : WordTrace (prefixWord ++ tailWord_4451321) baseStart_4451321 baseEnd_4451321 := by
    simpa [prefixWord, tailWord_4451321, baseEnd_4451321] using wordTrace_append hprefix tailTrace_4451321
  have hstable : (prefixWord ++ tailWord_4451321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451321).length < 2 ^ (prefixWord ++ tailWord_4451321).sum := by decide
  have hdescent : baseEnd_4451321 < baseStart_4451321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451418 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4451418 : Nat := 118140960795 + 4451418 * 2 ^ 59
def prefixEnd_4451418 : Nat := 4983230072969 + 3 ^ 40 * 4451418 * 2
def baseEnd_4451418 : Nat := 2285717028075770040303307

theorem tailTrace_4451418 : CollatzResearch.WordTrace tailWord_4451418 prefixEnd_4451418 2285717028075770040303307 := by
  unfold tailWord_4451418
  simp only [CollatzResearch.WordTrace]
  refine ⟨40589138146820075628394727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108237701724853535009052605 40589138146820075628394727)
  ·
    refine ⟨60883707220230113442592091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40589138146820075628394727 60883707220230113442592091)
    ·
      refine ⟨91325560830345170163888137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60883707220230113442592091 91325560830345170163888137)
      ·
        refine ⟨68494170622758877622916103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91325560830345170163888137 68494170622758877622916103)
        ·
          refine ⟨102741255934138316434374155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68494170622758877622916103 102741255934138316434374155)
          ·
            refine ⟨154111883901207474651561233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102741255934138316434374155 154111883901207474651561233)
            ·
              refine ⟨115583912925905605988670925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154111883901207474651561233 115583912925905605988670925)
              ·
                refine ⟨43343967347214602245751597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115583912925905605988670925 43343967347214602245751597)
                ·
                  refine ⟨16253987755205475842156849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43343967347214602245751597 16253987755205475842156849)
                  ·
                    refine ⟨12190490816404106881617637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16253987755205475842156849 12190490816404106881617637)
                    ·
                      refine ⟨2285717028075770040303307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12190490816404106881617637 2285717028075770040303307)
                      ·
                        rfl

theorem cell23_4451418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4451418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451418 prefixEnd_4451418 := by exact prefixLift 4451418
  have htrace : WordTrace (prefixWord ++ tailWord_4451418) baseStart_4451418 baseEnd_4451418 := by
    simpa [prefixWord, tailWord_4451418, baseEnd_4451418] using wordTrace_append hprefix tailTrace_4451418
  have hstable : (prefixWord ++ tailWord_4451418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451418).length < 2 ^ (prefixWord ++ tailWord_4451418).sum := by decide
  have hdescent : baseEnd_4451418 < baseStart_4451418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451439 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 1, 2, 2]
def baseStart_4451439 : Nat := 118140960795 + 4451439 * 2 ^ 59
def prefixEnd_4451439 : Nat := 4983230072969 + 3 ^ 40 * 4451439 * 2
def baseEnd_4451439 : Nat := 2285727811169514458140711

theorem tailTrace_4451439 : CollatzResearch.WordTrace tailWord_4451439 prefixEnd_4451439 2285727811169514458140711 := by
  unfold tailWord_4451439
  simp only [CollatzResearch.WordTrace]
  refine ⟨162357318520204223100093371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108238212346802815400062247 162357318520204223100093371)
  ·
    refine ⟨243535977780306334650140057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162357318520204223100093371 243535977780306334650140057)
    ·
      refine ⟨182651983335229750987605043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243535977780306334650140057 182651983335229750987605043)
      ·
        refine ⟨273977975002844626481407565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182651983335229750987605043 273977975002844626481407565)
        ·
          refine ⟨102741740626066734930527837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273977975002844626481407565 102741740626066734930527837)
          ·
            refine ⟨38528152734775025598947939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102741740626066734930527837 38528152734775025598947939)
            ·
              refine ⟨57792229102162538398421909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38528152734775025598947939 57792229102162538398421909)
              ·
                refine ⟨2709010739163868987426027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57792229102162538398421909 2709010739163868987426027)
                ·
                  refine ⟨4063516108745803481139041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709010739163868987426027 4063516108745803481139041)
                  ·
                    refine ⟨3047637081559352610854281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063516108745803481139041 3047637081559352610854281)
                    ·
                      refine ⟨2285727811169514458140711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047637081559352610854281 2285727811169514458140711)
                      ·
                        rfl

theorem cell23_4451439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 2, 2].length) (baseStart_4451439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451439 prefixEnd_4451439 := by exact prefixLift 4451439
  have htrace : WordTrace (prefixWord ++ tailWord_4451439) baseStart_4451439 baseEnd_4451439 := by
    simpa [prefixWord, tailWord_4451439, baseEnd_4451439] using wordTrace_append hprefix tailTrace_4451439
  have hstable : (prefixWord ++ tailWord_4451439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451439).length < 2 ^ (prefixWord ++ tailWord_4451439).sum := by decide
  have hdescent : baseEnd_4451439 < baseStart_4451439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451449 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_4451449 : Nat := 118140960795 + 4451449 * 2 ^ 59
def prefixEnd_4451449 : Nat := 4983230072969 + 3 ^ 40 * 4451449 * 2
def baseEnd_4451449 : Nat := 761910981992019806338555

theorem tailTrace_4451449 : CollatzResearch.WordTrace tailWord_4451449 prefixEnd_4451449 761910981992019806338555 := by
  unfold tailWord_4451449
  simp only [CollatzResearch.WordTrace]
  refine ⟨162357683250167994807957401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108238455500111996538638267 162357683250167994807957401)
  ·
    refine ⟨121768262437625996105968051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162357683250167994807957401 121768262437625996105968051)
    ·
      refine ⟨182652393656438994158952077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121768262437625996105968051 182652393656438994158952077)
      ·
        refine ⟨68494647621164622809607029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182652393656438994158952077 68494647621164622809607029)
        ·
          refine ⟨6421373214484183388400659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68494647621164622809607029 6421373214484183388400659)
          ·
            refine ⟨9632059821726275082600989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421373214484183388400659 9632059821726275082600989)
            ·
              refine ⟨3612022433147353155975371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9632059821726275082600989 3612022433147353155975371)
              ·
                refine ⟨5418033649721029733963057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612022433147353155975371 5418033649721029733963057)
                ·
                  refine ⟨4063525237290772300472293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418033649721029733963057 4063525237290772300472293)
                  ·
                    refine ⟨761910981992019806338555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063525237290772300472293 761910981992019806338555)
                    ·
                      rfl

theorem cell23_4451449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_4451449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451449 prefixEnd_4451449 := by exact prefixLift 4451449
  have htrace : WordTrace (prefixWord ++ tailWord_4451449) baseStart_4451449 baseEnd_4451449 := by
    simpa [prefixWord, tailWord_4451449, baseEnd_4451449] using wordTrace_append hprefix tailTrace_4451449
  have hstable : (prefixWord ++ tailWord_4451449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451449).length < 2 ^ (prefixWord ++ tailWord_4451449).sum := by decide
  have hdescent : baseEnd_4451449 < baseStart_4451449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451490 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4451490 : Nat := 118140960795 + 4451490 * 2 ^ 59
def prefixEnd_4451490 : Nat := 4983230072969 + 3 ^ 40 * 4451490 * 2
def baseEnd_4451490 : Nat := 2285753998682893758602977

theorem tailTrace_4451490 : CollatzResearch.WordTrace tailWord_4451490 prefixEnd_4451490 2285753998682893758602977 := by
  unfold tailWord_4451490
  simp only [CollatzResearch.WordTrace]
  refine ⟨40589794660754864702549981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108239452428679639206799949 40589794660754864702549981)
  ·
    refine ⟨15221172997783074263456243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40589794660754864702549981 15221172997783074263456243)
    ·
      refine ⟨22831759496674611395184365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15221172997783074263456243 22831759496674611395184365)
      ·
        refine ⟨8561909811252979273194137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22831759496674611395184365 8561909811252979273194137)
        ·
          refine ⟨6421432358439734454895603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561909811252979273194137 6421432358439734454895603)
          ·
            refine ⟨9632148537659601682343405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421432358439734454895603 9632148537659601682343405)
            ·
              refine ⟨3612055701622350630878777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9632148537659601682343405 3612055701622350630878777)
              ·
                refine ⟨2709041776216762973159083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612055701622350630878777 2709041776216762973159083)
                ·
                  refine ⟨4063562664325144459738625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709041776216762973159083 4063562664325144459738625)
                  ·
                    refine ⟨3047671998243858344803969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063562664325144459738625 3047671998243858344803969)
                    ·
                      refine ⟨2285753998682893758602977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047671998243858344803969 2285753998682893758602977)
                      ·
                        rfl

theorem cell23_4451490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4451490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451490 prefixEnd_4451490 := by exact prefixLift 4451490
  have htrace : WordTrace (prefixWord ++ tailWord_4451490) baseStart_4451490 baseEnd_4451490 := by
    simpa [prefixWord, tailWord_4451490, baseEnd_4451490] using wordTrace_append hprefix tailTrace_4451490
  have hstable : (prefixWord ++ tailWord_4451490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451490).length < 2 ^ (prefixWord ++ tailWord_4451490).sum := by decide
  have hdescent : baseEnd_4451490 < baseStart_4451490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451506 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_4451506 : Nat := 118140960795 + 4451506 * 2 ^ 59
def prefixEnd_4451506 : Nat := 4983230072969 + 3 ^ 40 * 4451506 * 2
def baseEnd_4451506 : Nat := 2285762214373365696002903

theorem tailTrace_4451506 : CollatzResearch.WordTrace tailWord_4451506 prefixEnd_4451506 2285762214373365696002903 := by
  unfold tailWord_4451506
  simp only [CollatzResearch.WordTrace]
  refine ⟨40589940552740373385695593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108239841473974329028521581 40589940552740373385695593)
  ·
    refine ⟨30442455414555280039271695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40589940552740373385695593 30442455414555280039271695)
    ·
      refine ⟨45663683121832920058907543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30442455414555280039271695 45663683121832920058907543)
      ·
        refine ⟨68495524682749380088361315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45663683121832920058907543 68495524682749380088361315)
        ·
          refine ⟨102743287024124070132541973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68495524682749380088361315 102743287024124070132541973)
          ·
            refine ⟨4816091579255815787462905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102743287024124070132541973 4816091579255815787462905)
            ·
              refine ⟨3612068684441861840597179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816091579255815787462905 3612068684441861840597179)
              ·
                refine ⟨5418103026662792760895769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612068684441861840597179 5418103026662792760895769)
                ·
                  refine ⟨4063577269997094570671827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418103026662792760895769 4063577269997094570671827)
                  ·
                    refine ⟨6095365904995641856007741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063577269997094570671827 6095365904995641856007741)
                    ·
                      refine ⟨2285762214373365696002903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095365904995641856007741 2285762214373365696002903)
                      ·
                        rfl

theorem cell23_4451506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_4451506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451506 prefixEnd_4451506 := by exact prefixLift 4451506
  have htrace : WordTrace (prefixWord ++ tailWord_4451506) baseStart_4451506 baseEnd_4451506 := by
    simpa [prefixWord, tailWord_4451506, baseEnd_4451506] using wordTrace_append hprefix tailTrace_4451506
  have hstable : (prefixWord ++ tailWord_4451506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451506).length < 2 ^ (prefixWord ++ tailWord_4451506).sum := by decide
  have hdescent : baseEnd_4451506 < baseStart_4451506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451510 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4451510 : Nat := 118140960795 + 4451510 * 2 ^ 59
def prefixEnd_4451510 : Nat := 4983230072969 + 3 ^ 40 * 4451510 * 2
def baseEnd_4451510 : Nat := 2285764268295983680352885

theorem tailTrace_4451510 : CollatzResearch.WordTrace tailWord_4451510 prefixEnd_4451510 2285764268295983680352885 := by
  unfold tailWord_4451510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147494256434187639120499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108239938735298001483951989 10147494256434187639120499)
  ·
    refine ⟨15221241384651281458680749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147494256434187639120499 15221241384651281458680749)
    ·
      refine ⟨5707965519244230547005281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15221241384651281458680749 5707965519244230547005281)
      ·
        refine ⟨4280974139433172910253961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5707965519244230547005281 4280974139433172910253961)
        ·
          refine ⟨3210730604574879682690471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280974139433172910253961 3210730604574879682690471)
          ·
            refine ⟨4816095906862319524035707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210730604574879682690471 4816095906862319524035707)
            ·
              refine ⟨7224143860293479286053561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816095906862319524035707 7224143860293479286053561)
              ·
                refine ⟨5418107895220109464540171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224143860293479286053561 5418107895220109464540171)
                ·
                  refine ⟨8127161842830164196810257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418107895220109464540171 8127161842830164196810257)
                  ·
                    refine ⟨6095371382122623147607693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8127161842830164196810257 6095371382122623147607693)
                    ·
                      refine ⟨2285764268295983680352885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095371382122623147607693 2285764268295983680352885)
                      ·
                        rfl

theorem cell23_4451510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4451510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451510 prefixEnd_4451510 := by exact prefixLift 4451510
  have htrace : WordTrace (prefixWord ++ tailWord_4451510) baseStart_4451510 baseEnd_4451510 := by
    simpa [prefixWord, tailWord_4451510, baseEnd_4451510] using wordTrace_append hprefix tailTrace_4451510
  have hstable : (prefixWord ++ tailWord_4451510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451510).length < 2 ^ (prefixWord ++ tailWord_4451510).sum := by decide
  have hdescent : baseEnd_4451510 < baseStart_4451510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451512 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_4451512 : Nat := 118140960795 + 4451512 * 2 ^ 59
def prefixEnd_4451512 : Nat := 4983230072969 + 3 ^ 40 * 4451512 * 2
def baseEnd_4451512 : Nat := 2285765295257292672527875

theorem tailTrace_4451512 : CollatzResearch.WordTrace tailWord_4451512 prefixEnd_4451512 2285765295257292672527875 := by
  unfold tailWord_4451512
  simp only [CollatzResearch.WordTrace]
  refine ⟨81179990524469878283750395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108239987365959837711667193 81179990524469878283750395)
  ·
    refine ⟨121769985786704817425625593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81179990524469878283750395 121769985786704817425625593)
    ·
      refine ⟨91327489340028613069219195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121769985786704817425625593 91327489340028613069219195)
      ·
        refine ⟨136991234010042919603828793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91327489340028613069219195 136991234010042919603828793)
        ·
          refine ⟨102743425507532189702871595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136991234010042919603828793 102743425507532189702871595)
          ·
            refine ⟨154115138261298284554307393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102743425507532189702871595 154115138261298284554307393)
            ·
              refine ⟨115586353695973713415730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154115138261298284554307393 115586353695973713415730545)
              ·
                refine ⟨86689765271980285061797909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115586353695973713415730545 86689765271980285061797909)
                ·
                  refine ⟨4063582747124075862271777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86689765271980285061797909 4063582747124075862271777)
                  ·
                    refine ⟨3047687060343056896703833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063582747124075862271777 3047687060343056896703833)
                    ·
                      refine ⟨2285765295257292672527875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047687060343056896703833 2285765295257292672527875)
                      ·
                        rfl

theorem cell23_4451512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_4451512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451512 prefixEnd_4451512 := by exact prefixLift 4451512
  have htrace : WordTrace (prefixWord ++ tailWord_4451512) baseStart_4451512 baseEnd_4451512 := by
    simpa [prefixWord, tailWord_4451512, baseEnd_4451512] using wordTrace_append hprefix tailTrace_4451512
  have hstable : (prefixWord ++ tailWord_4451512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451512).length < 2 ^ (prefixWord ++ tailWord_4451512).sum := by decide
  have hdescent : baseEnd_4451512 < baseStart_4451512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451516 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_4451516 : Nat := 118140960795 + 4451516 * 2 ^ 59
def prefixEnd_4451516 : Nat := 4983230072969 + 3 ^ 40 * 4451516 * 2
def baseEnd_4451516 : Nat := 2285767349179910656877857

theorem tailTrace_4451516 : CollatzResearch.WordTrace tailWord_4451516 prefixEnd_4451516 2285767349179910656877857 := by
  unfold tailWord_4451516
  simp only [CollatzResearch.WordTrace]
  refine ⟨81180063470462632625323201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108240084627283510167097601 81180063470462632625323201)
  ·
    refine ⟨60885047602846974468992401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81180063470462632625323201 60885047602846974468992401)
    ·
      refine ⟨45663785702135230851744301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60885047602846974468992401 45663785702135230851744301)
      ·
        refine ⟨17123919638300711569404113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45663785702135230851744301 17123919638300711569404113)
        ·
          refine ⟨12842939728725533677053085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17123919638300711569404113 12842939728725533677053085)
          ·
            refine ⟨4816102398272075128894907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12842939728725533677053085 4816102398272075128894907)
            ·
              refine ⟨7224153597408112693342361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816102398272075128894907 7224153597408112693342361)
              ·
                refine ⟨5418115198056084520006771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224153597408112693342361 5418115198056084520006771)
                ·
                  refine ⟨8127172797084126780010157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418115198056084520006771 8127172797084126780010157)
                  ·
                    refine ⟨3047689798906547542503809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8127172797084126780010157 3047689798906547542503809)
                    ·
                      refine ⟨2285767349179910656877857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047689798906547542503809 2285767349179910656877857)
                      ·
                        rfl

theorem cell23_4451516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_4451516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451516 prefixEnd_4451516 := by exact prefixLift 4451516
  have htrace : WordTrace (prefixWord ++ tailWord_4451516) baseStart_4451516 baseEnd_4451516 := by
    simpa [prefixWord, tailWord_4451516, baseEnd_4451516] using wordTrace_append hprefix tailTrace_4451516
  have hstable : (prefixWord ++ tailWord_4451516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451516).length < 2 ^ (prefixWord ++ tailWord_4451516).sum := by decide
  have hdescent : baseEnd_4451516 < baseStart_4451516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451545 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_4451545 : Nat := 118140960795 + 4451545 * 2 ^ 59
def prefixEnd_4451545 : Nat := 4983230072969 + 3 ^ 40 * 4451545 * 2
def baseEnd_4451545 : Nat := 2285782240118891043415223

theorem tailTrace_4451545 : CollatzResearch.WordTrace tailWord_4451545 prefixEnd_4451545 2285782240118891043415223 := by
  unfold tailWord_4451545
  simp only [CollatzResearch.WordTrace]
  refine ⟨162361184657820203203452089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108240789771880135468968059 162361184657820203203452089)
  ·
    refine ⟨121770888493365152402589067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162361184657820203203452089 121770888493365152402589067)
    ·
      refine ⟨182656332740047728603883601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121770888493365152402589067 182656332740047728603883601)
      ·
        refine ⟨136992249555035796452912701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182656332740047728603883601 136992249555035796452912701)
        ·
          refine ⟨51372093583138423669842263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136992249555035796452912701 51372093583138423669842263)
          ·
            refine ⟨77058140374707635504763395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51372093583138423669842263 77058140374707635504763395)
            ·
              refine ⟨115587210562061453257145093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77058140374707635504763395 115587210562061453257145093)
              ·
                refine ⟨21672601980386522485714705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115587210562061453257145093 21672601980386522485714705)
                ·
                  refine ⟨16254451485289891864286029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21672601980386522485714705 16254451485289891864286029)
                  ·
                    refine ⟨6095419306983709449107261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16254451485289891864286029 6095419306983709449107261)
                    ·
                      refine ⟨2285782240118891043415223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095419306983709449107261 2285782240118891043415223)
                      ·
                        rfl

theorem cell23_4451545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_4451545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451545 prefixEnd_4451545 := by exact prefixLift 4451545
  have htrace : WordTrace (prefixWord ++ tailWord_4451545) baseStart_4451545 baseEnd_4451545 := by
    simpa [prefixWord, tailWord_4451545, baseEnd_4451545] using wordTrace_append hprefix tailTrace_4451545
  have hstable : (prefixWord ++ tailWord_4451545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451545).length < 2 ^ (prefixWord ++ tailWord_4451545).sum := by decide
  have hdescent : baseEnd_4451545 < baseStart_4451545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451552 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 5]
def baseStart_4451552 : Nat := 118140960795 + 4451552 * 2 ^ 59
def prefixEnd_4451552 : Nat := 4983230072969 + 3 ^ 40 * 4451552 * 2
def baseEnd_4451552 : Nat := 253976203831496946225299

theorem tailTrace_4451552 : CollatzResearch.WordTrace tailWord_4451552 prefixEnd_4451552 253976203831496946225299 := by
  unfold tailWord_4451552
  simp only [CollatzResearch.WordTrace]
  refine ⟨81180719984397421699478455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108240959979196562265971273 81180719984397421699478455)
  ·
    refine ⟨121771079976596132549217683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81180719984397421699478455 121771079976596132549217683)
    ·
      refine ⟨182656619964894198823826525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121771079976596132549217683 182656619964894198823826525)
      ·
        refine ⟨68496232486835324558934947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182656619964894198823826525 68496232486835324558934947)
        ·
          refine ⟨102744348730252986838402421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68496232486835324558934947 102744348730252986838402421)
          ·
            refine ⟨9632282693461217516100227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102744348730252986838402421 9632282693461217516100227)
            ·
              refine ⟨14448424040191826274150341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632282693461217516100227 14448424040191826274150341)
              ·
                refine ⟨2709079507535967426403189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14448424040191826274150341 2709079507535967426403189)
                ·
                  refine ⟨253976203831496946225299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2709079507535967426403189 253976203831496946225299)
                  ·
                    rfl

theorem cell23_4451552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 5].length) (baseStart_4451552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451552 prefixEnd_4451552 := by exact prefixLift 4451552
  have htrace : WordTrace (prefixWord ++ tailWord_4451552) baseStart_4451552 baseEnd_4451552 := by
    simpa [prefixWord, tailWord_4451552, baseEnd_4451552] using wordTrace_append hprefix tailTrace_4451552
  have hstable : (prefixWord ++ tailWord_4451552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451552).length < 2 ^ (prefixWord ++ tailWord_4451552).sum := by decide
  have hdescent : baseEnd_4451552 < baseStart_4451552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451562 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_4451562 : Nat := 118140960795 + 4451562 * 2 ^ 59
def prefixEnd_4451562 : Nat := 4983230072969 + 3 ^ 40 * 4451562 * 2
def baseEnd_4451562 : Nat := 2285790969290017476902645

theorem tailTrace_4451562 : CollatzResearch.WordTrace tailWord_4451562 prefixEnd_4451562 2285790969290017476902645 := by
  unfold tailWord_4451562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40590451174689653776705235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108241203132505743404547293 40590451174689653776705235)
  ·
    refine ⟨60885676762034480665057853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40590451174689653776705235 60885676762034480665057853)
    ·
      refine ⟨22832128785762930249396695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60885676762034480665057853 22832128785762930249396695)
      ·
        refine ⟨34248193178644395374095043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22832128785762930249396695 34248193178644395374095043)
        ·
          refine ⟨51372289767966593061142565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34248193178644395374095043 51372289767966593061142565)
          ·
            refine ⟨9632304331493736198964231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51372289767966593061142565 9632304331493736198964231)
            ·
              refine ⟨14448456497240604298446347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632304331493736198964231 14448456497240604298446347)
              ·
                refine ⟨21672684745860906447669521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14448456497240604298446347 21672684745860906447669521)
                ·
                  refine ⟨16254513559395679835752141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21672684745860906447669521 16254513559395679835752141)
                  ·
                    refine ⟨6095442584773379938407053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16254513559395679835752141 6095442584773379938407053)
                    ·
                      refine ⟨2285790969290017476902645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095442584773379938407053 2285790969290017476902645)
                      ·
                        rfl

theorem cell23_4451562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_4451562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451562 prefixEnd_4451562 := by exact prefixLift 4451562
  have htrace : WordTrace (prefixWord ++ tailWord_4451562) baseStart_4451562 baseEnd_4451562 := by
    simpa [prefixWord, tailWord_4451562, baseEnd_4451562] using wordTrace_append hprefix tailTrace_4451562
  have hstable : (prefixWord ++ tailWord_4451562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451562).length < 2 ^ (prefixWord ++ tailWord_4451562).sum := by decide
  have hdescent : baseEnd_4451562 < baseStart_4451562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451582 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4451582 : Nat := 118140960795 + 4451582 * 2 ^ 59
def prefixEnd_4451582 : Nat := 4983230072969 + 3 ^ 40 * 4451582 * 2
def baseEnd_4451582 : Nat := 761933746301035799550851

theorem tailTrace_4451582 : CollatzResearch.WordTrace tailWord_4451582 prefixEnd_4451582 761933746301035799550851 := by
  unfold tailWord_4451582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20295316769835769815318625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108241689439124105681699333 20295316769835769815318625)
  ·
    refine ⟨15221487577376827361488969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20295316769835769815318625 15221487577376827361488969)
    ·
      refine ⟨11416115683032620521116727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15221487577376827361488969 11416115683032620521116727)
      ·
        refine ⟨17124173524548930781675091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11416115683032620521116727 17124173524548930781675091)
        ·
          refine ⟨25686260286823396172512637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17124173524548930781675091 25686260286823396172512637)
          ·
            refine ⟨9632347607558773564692239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25686260286823396172512637 9632347607558773564692239)
            ·
              refine ⟨14448521411338160347038359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632347607558773564692239 14448521411338160347038359)
              ·
                refine ⟨21672782117007240520557539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14448521411338160347038359 21672782117007240520557539)
                ·
                  refine ⟨32509173175510860780836309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21672782117007240520557539 32509173175510860780836309)
                  ·
                    refine ⟨761933746301035799550851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32509173175510860780836309 761933746301035799550851)
                    ·
                      rfl

theorem cell23_4451582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4451582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451582 prefixEnd_4451582 := by exact prefixLift 4451582
  have htrace : WordTrace (prefixWord ++ tailWord_4451582) baseStart_4451582 baseEnd_4451582 := by
    simpa [prefixWord, tailWord_4451582, baseEnd_4451582] using wordTrace_append hprefix tailTrace_4451582
  have hstable : (prefixWord ++ tailWord_4451582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451582).length < 2 ^ (prefixWord ++ tailWord_4451582).sum := by decide
  have hdescent : baseEnd_4451582 < baseStart_4451582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451586 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4451586 : Nat := 118140960795 + 4451586 * 2 ^ 59
def prefixEnd_4451586 : Nat := 4983230072969 + 3 ^ 40 * 4451586 * 2
def baseEnd_4451586 : Nat := 253978143647302820333615

theorem tailTrace_4451586 : CollatzResearch.WordTrace tailWord_4451586 prefixEnd_4451586 253978143647302820333615 := by
  unfold tailWord_4451586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40590670012667916801423653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108241786700447778137129741 40590670012667916801423653)
  ·
    refine ⟨7610750627375234400266935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40590670012667916801423653 7610750627375234400266935)
    ·
      refine ⟨11416125941062851600400403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610750627375234400266935 11416125941062851600400403)
      ·
        refine ⟨17124188911594277400600605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11416125941062851600400403 17124188911594277400600605)
        ·
          refine ⟨6421570841847854025225227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17124188911594277400600605 6421570841847854025225227)
          ·
            refine ⟨9632356262771781037837841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421570841847854025225227 9632356262771781037837841)
            ·
              refine ⟨7224267197078835778378381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9632356262771781037837841 7224267197078835778378381)
              ·
                refine ⟨2709100198904563416891893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7224267197078835778378381 2709100198904563416891893)
                ·
                  refine ⟨253978143647302820333615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2709100198904563416891893 253978143647302820333615)
                  ·
                    rfl

theorem cell23_4451586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4451586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451586 prefixEnd_4451586 := by exact prefixLift 4451586
  have htrace : WordTrace (prefixWord ++ tailWord_4451586) baseStart_4451586 baseEnd_4451586 := by
    simpa [prefixWord, tailWord_4451586, baseEnd_4451586] using wordTrace_append hprefix tailTrace_4451586
  have hstable : (prefixWord ++ tailWord_4451586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451586).length < 2 ^ (prefixWord ++ tailWord_4451586).sum := by decide
  have hdescent : baseEnd_4451586 < baseStart_4451586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451612 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_4451612 : Nat := 118140960795 + 4451612 * 2 ^ 59
def prefixEnd_4451612 : Nat := 4983230072969 + 3 ^ 40 * 4451612 * 2
def baseEnd_4451612 : Nat := 761938881107580760425805

theorem tailTrace_4451612 : CollatzResearch.WordTrace tailWord_4451612 prefixEnd_4451612 761938881107580760425805 := by
  unfold tailWord_4451612
  simp only [CollatzResearch.WordTrace]
  refine ⟨81181814174288736823070545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108242418899051649097427393 81181814174288736823070545)
  ·
    refine ⟨60886360630716552617302909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81181814174288736823070545 60886360630716552617302909)
    ·
      refine ⟨22832385236518707231488591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60886360630716552617302909 22832385236518707231488591)
      ·
        refine ⟨34248577854778060847232887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22832385236518707231488591 34248577854778060847232887)
        ·
          refine ⟨51372866782167091270849331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34248577854778060847232887 51372866782167091270849331)
          ·
            refine ⟨77059300173250636906273997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51372866782167091270849331 77059300173250636906273997)
            ·
              refine ⟨28897237564968988839852749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77059300173250636906273997 28897237564968988839852749)
              ·
                refine ⟨10836464086863370814944781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28897237564968988839852749 10836464086863370814944781)
                ·
                  refine ⟨4063674032573764055604293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10836464086863370814944781 4063674032573764055604293)
                  ·
                    refine ⟨761938881107580760425805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063674032573764055604293 761938881107580760425805)
                    ·
                      rfl

theorem cell23_4451612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_4451612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451612 prefixEnd_4451612 := by exact prefixLift 4451612
  have htrace : WordTrace (prefixWord ++ tailWord_4451612) baseStart_4451612 baseEnd_4451612 := by
    simpa [prefixWord, tailWord_4451612, baseEnd_4451612] using wordTrace_append hprefix tailTrace_4451612
  have hstable : (prefixWord ++ tailWord_4451612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451612).length < 2 ^ (prefixWord ++ tailWord_4451612).sum := by decide
  have hdescent : baseEnd_4451612 < baseStart_4451612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451715 : List Nat := [1, 1, 1, 3, 5, 12]
def baseStart_4451715 : Nat := 118140960795 + 4451715 * 2 ^ 59
def prefixEnd_4451715 : Nat := 4983230072969 + 3 ^ 40 * 4451715 * 2
def baseEnd_4451715 : Nat := 9406870501358664108187

theorem tailTrace_4451715 : CollatzResearch.WordTrace tailWord_4451715 prefixEnd_4451715 9406870501358664108187 := by
  unfold tailWord_4451715
  simp only [CollatzResearch.WordTrace]
  refine ⟨162367385067204322237140599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108244923378136214824760399 162367385067204322237140599)
  ·
    refine ⟨243551077600806483355710899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162367385067204322237140599 243551077600806483355710899)
    ·
      refine ⟨365326616401209725033566349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243551077600806483355710899 365326616401209725033566349)
      ·
        refine ⟨136997481150453646887587381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365326616401209725033566349 136997481150453646887587381)
        ·
          refine ⟨12843513857855029395711317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136997481150453646887587381 12843513857855029395711317)
          ·
            refine ⟨9406870501358664108187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12843513857855029395711317 9406870501358664108187)
            ·
              rfl

theorem cell23_4451715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 12].length) (baseStart_4451715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451715 prefixEnd_4451715 := by exact prefixLift 4451715
  have htrace : WordTrace (prefixWord ++ tailWord_4451715) baseStart_4451715 baseEnd_4451715 := by
    simpa [prefixWord, tailWord_4451715, baseEnd_4451715] using wordTrace_append hprefix tailTrace_4451715
  have hstable : (prefixWord ++ tailWord_4451715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451715).length < 2 ^ (prefixWord ++ tailWord_4451715).sum := by decide
  have hdescent : baseEnd_4451715 < baseStart_4451715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451719 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 2, 4]
def baseStart_4451719 : Nat := 118140960795 + 4451719 * 2 ^ 59
def prefixEnd_4451719 : Nat := 4983230072969 + 3 ^ 40 * 4451719 * 2
def baseEnd_4451719 : Nat := 761957195250924454213141

theorem tailTrace_4451719 : CollatzResearch.WordTrace tailWord_4451719 prefixEnd_4451719 761957195250924454213141 := by
  unfold tailWord_4451719
  simp only [CollatzResearch.WordTrace]
  refine ⟨162367530959189830920286211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108245020639459887280190807 162367530959189830920286211)
  ·
    refine ⟨243551296438784746380429317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162367530959189830920286211 243551296438784746380429317)
    ·
      refine ⟨45665868082272139946330497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243551296438784746380429317 45665868082272139946330497)
      ·
        refine ⟨34249401061704104959747873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45665868082272139946330497 34249401061704104959747873)
        ·
          refine ⟨25687050796278078719810905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34249401061704104959747873 25687050796278078719810905)
          ·
            refine ⟨19265288097208559039858179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25687050796278078719810905 19265288097208559039858179)
            ·
              refine ⟨28897932145812838559787269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19265288097208559039858179 28897932145812838559787269)
              ·
                refine ⟨5418362277339907229960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28897932145812838559787269 5418362277339907229960113)
                ·
                  refine ⟨4063771708004930422470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418362277339907229960113 4063771708004930422470085)
                  ·
                    refine ⟨761957195250924454213141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063771708004930422470085 761957195250924454213141)
                    ·
                      rfl

theorem cell23_4451719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_4451719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451719 prefixEnd_4451719 := by exact prefixLift 4451719
  have htrace : WordTrace (prefixWord ++ tailWord_4451719) baseStart_4451719 baseEnd_4451719 := by
    simpa [prefixWord, tailWord_4451719, baseEnd_4451719] using wordTrace_append hprefix tailTrace_4451719
  have hstable : (prefixWord ++ tailWord_4451719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451719).length < 2 ^ (prefixWord ++ tailWord_4451719).sum := by decide
  have hdescent : baseEnd_4451719 < baseStart_4451719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451720 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4451720 : Nat := 118140960795 + 4451720 * 2 ^ 59
def prefixEnd_4451720 : Nat := 4983230072969 + 3 ^ 40 * 4451720 * 2
def baseEnd_4451720 : Nat := 2285872099233427858726919

theorem tailTrace_4451720 : CollatzResearch.WordTrace tailWord_4451720 prefixEnd_4451720 2285872099233427858726919 := by
  unfold tailWord_4451720
  simp only [CollatzResearch.WordTrace]
  refine ⟨81183783716093104045536307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108245044954790805394048409 81183783716093104045536307)
  ·
    refine ⟨121775675574139656068304461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81183783716093104045536307 121775675574139656068304461)
    ·
      refine ⟨45665878340302371025614173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121775675574139656068304461 45665878340302371025614173)
      ·
        refine ⟨17124704377613389134605315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45665878340302371025614173 17124704377613389134605315)
        ·
          refine ⟨25687056566420083701907973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17124704377613389134605315 25687056566420083701907973)
          ·
            refine ⟨4816323106203765694107745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25687056566420083701907973 4816323106203765694107745)
            ·
              refine ⟨3612242329652824270580809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816323106203765694107745 3612242329652824270580809)
              ·
                refine ⟨2709181747239618202935607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612242329652824270580809 2709181747239618202935607)
                ·
                  refine ⟨4063772620859427304403411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709181747239618202935607 4063772620859427304403411)
                  ·
                    refine ⟨6095658931289140956605117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063772620859427304403411 6095658931289140956605117)
                    ·
                      refine ⟨2285872099233427858726919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095658931289140956605117 2285872099233427858726919)
                      ·
                        rfl

theorem cell23_4451720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4451720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451720 prefixEnd_4451720 := by exact prefixLift 4451720
  have htrace : WordTrace (prefixWord ++ tailWord_4451720) baseStart_4451720 baseEnd_4451720 := by
    simpa [prefixWord, tailWord_4451720, baseEnd_4451720] using wordTrace_append hprefix tailTrace_4451720
  have hstable : (prefixWord ++ tailWord_4451720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451720).length < 2 ^ (prefixWord ++ tailWord_4451720).sum := by decide
  have hdescent : baseEnd_4451720 < baseStart_4451720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451776 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_4451776 : Nat := 118140960795 + 4451776 * 2 ^ 59
def prefixEnd_4451776 : Nat := 4983230072969 + 3 ^ 40 * 4451776 * 2
def baseEnd_4451776 : Nat := 2285900854150079639626661

theorem tailTrace_4451776 : CollatzResearch.WordTrace tailWord_4451776 prefixEnd_4451776 2285900854150079639626661 := by
  unfold tailWord_4451776
  simp only [CollatzResearch.WordTrace]
  refine ⟨81184804959991664827555591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108246406613322219770074121 81184804959991664827555591)
  ·
    refine ⟨121777207439987497241333387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81184804959991664827555591 121777207439987497241333387)
    ·
      refine ⟨182665811159981245862000081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121777207439987497241333387 182665811159981245862000081)
      ·
        refine ⟨136999358369985934396500061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182665811159981245862000081 136999358369985934396500061)
        ·
          refine ⟨51374759388744725398687523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136999358369985934396500061 51374759388744725398687523)
          ·
            refine ⟨77062139083117088098031285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51374759388744725398687523 77062139083117088098031285)
            ·
              refine ⟨7224575539042227009190433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77062139083117088098031285 7224575539042227009190433)
              ·
                refine ⟨5418431654281670256892825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224575539042227009190433 5418431654281670256892825)
                ·
                  refine ⟨4063823740711252692669619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418431654281670256892825 4063823740711252692669619)
                  ·
                    refine ⟨6095735611066879039004429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063823740711252692669619 6095735611066879039004429)
                    ·
                      refine ⟨2285900854150079639626661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095735611066879039004429 2285900854150079639626661)
                      ·
                        rfl

theorem cell23_4451776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_4451776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451776 prefixEnd_4451776 := by exact prefixLift 4451776
  have htrace : WordTrace (prefixWord ++ tailWord_4451776) baseStart_4451776 baseEnd_4451776 := by
    simpa [prefixWord, tailWord_4451776, baseEnd_4451776] using wordTrace_append hprefix tailTrace_4451776
  have hstable : (prefixWord ++ tailWord_4451776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451776).length < 2 ^ (prefixWord ++ tailWord_4451776).sum := by decide
  have hdescent : baseEnd_4451776 < baseStart_4451776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451812 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_4451812 : Nat := 118140960795 + 4451812 * 2 ^ 59
def prefixEnd_4451812 : Nat := 4983230072969 + 3 ^ 40 * 4451812 * 2
def baseEnd_4451812 : Nat := 2285919339453641498776495

theorem tailTrace_4451812 : CollatzResearch.WordTrace tailWord_4451812 prefixEnd_4451812 2285919339453641498776495 := by
  unfold tailWord_4451812
  simp only [CollatzResearch.WordTrace]
  refine ⟨81185461473926453901710845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108247281965235271868947793 81185461473926453901710845)
  ·
    refine ⟨30444548052722420213141567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81185461473926453901710845 30444548052722420213141567)
    ·
      refine ⟨45666822079083630319712351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30444548052722420213141567 45666822079083630319712351)
      ·
        refine ⟨68500233118625445479568527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45666822079083630319712351 68500233118625445479568527)
        ·
          refine ⟨102750349677938168219352791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68500233118625445479568527 102750349677938168219352791)
          ·
            refine ⟨154125524516907252329029187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102750349677938168219352791 154125524516907252329029187)
            ·
              refine ⟨231188286775360878493543781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154125524516907252329029187 231188286775360878493543781)
              ·
                refine ⟨43347803770380164717539459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231188286775360878493543781 43347803770380164717539459)
                ·
                  refine ⟨65021705655570247076309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43347803770380164717539459 65021705655570247076309189)
                  ·
                    refine ⟨12191569810419421326807973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65021705655570247076309189 12191569810419421326807973)
                    ·
                      refine ⟨2285919339453641498776495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12191569810419421326807973 2285919339453641498776495)
                      ·
                        rfl

theorem cell23_4451812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_4451812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451812 prefixEnd_4451812 := by exact prefixLift 4451812
  have htrace : WordTrace (prefixWord ++ tailWord_4451812) baseStart_4451812 baseEnd_4451812 := by
    simpa [prefixWord, tailWord_4451812, baseEnd_4451812] using wordTrace_append hprefix tailTrace_4451812
  have hstable : (prefixWord ++ tailWord_4451812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451812).length < 2 ^ (prefixWord ++ tailWord_4451812).sum := by decide
  have hdescent : baseEnd_4451812 < baseStart_4451812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451816 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4451816 : Nat := 118140960795 + 4451816 * 2 ^ 59
def prefixEnd_4451816 : Nat := 4983230072969 + 3 ^ 40 * 4451816 * 2
def baseEnd_4451816 : Nat := 2285921393376259483126477

theorem tailTrace_4451816 : CollatzResearch.WordTrace tailWord_4451816 prefixEnd_4451816 2285921393376259483126477 := by
  unfold tailWord_4451816
  simp only [CollatzResearch.WordTrace]
  refine ⟨81185534419919208243283651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108247379226558944324378201 81185534419919208243283651)
  ·
    refine ⟨121778301629878812364925477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81185534419919208243283651 121778301629878812364925477)
    ·
      refine ⟨22833431555602277318423527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121778301629878812364925477 22833431555602277318423527)
      ·
        refine ⟨34250147333403415977635291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22833431555602277318423527 34250147333403415977635291)
        ·
          refine ⟨51375221000105123966452937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34250147333403415977635291 51375221000105123966452937)
          ·
            refine ⟨38531415750078842974839703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51375221000105123966452937 38531415750078842974839703)
            ·
              refine ⟨57797123625118264462259555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38531415750078842974839703 57797123625118264462259555)
              ·
                refine ⟨86695685437677396693389333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57797123625118264462259555 86695685437677396693389333)
                ·
                  refine ⟨4063860254891127970002625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86695685437677396693389333 4063860254891127970002625)
                  ·
                    refine ⟨3047895191168345977501969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063860254891127970002625 3047895191168345977501969)
                    ·
                      refine ⟨2285921393376259483126477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047895191168345977501969 2285921393376259483126477)
                      ·
                        rfl

theorem cell23_4451816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4451816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451816 prefixEnd_4451816 := by exact prefixLift 4451816
  have htrace : WordTrace (prefixWord ++ tailWord_4451816) baseStart_4451816 baseEnd_4451816 := by
    simpa [prefixWord, tailWord_4451816, baseEnd_4451816] using wordTrace_append hprefix tailTrace_4451816
  have hstable : (prefixWord ++ tailWord_4451816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451816).length < 2 ^ (prefixWord ++ tailWord_4451816).sum := by decide
  have hdescent : baseEnd_4451816 < baseStart_4451816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451850 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_4451850 : Nat := 118140960795 + 4451850 * 2 ^ 59
def prefixEnd_4451850 : Nat := 4983230072969 + 3 ^ 40 * 4451850 * 2
def baseEnd_4451850 : Nat := 2285938851718512350101321

theorem tailTrace_4451850 : CollatzResearch.WordTrace tailWord_4451850 prefixEnd_4451850 2285938851718512350101321 := by
  unfold tailWord_4451850
  simp only [CollatzResearch.WordTrace]
  refine ⟨40593077230428810073326251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108248205947810160195536669 40593077230428810073326251)
  ·
    refine ⟨60889615845643215109989377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40593077230428810073326251 60889615845643215109989377)
    ·
      refine ⟨45667211884232411332492033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60889615845643215109989377 45667211884232411332492033)
      ·
        refine ⟨34250408913174308499369025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45667211884232411332492033 34250408913174308499369025)
        ·
          refine ⟨25687806684880731374526769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34250408913174308499369025 25687806684880731374526769)
          ·
            refine ⟨19265855013660548530895077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25687806684880731374526769 19265855013660548530895077)
            ·
              refine ⟨3612347815061352849542827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19265855013660548530895077 3612347815061352849542827)
              ·
                refine ⟨5418521722592029274314241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612347815061352849542827 5418521722592029274314241)
                ·
                  refine ⟨4063891291944021955735681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418521722592029274314241 4063891291944021955735681)
                  ·
                    refine ⟨3047918468958016466801761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063891291944021955735681 3047918468958016466801761)
                    ·
                      refine ⟨2285938851718512350101321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3047918468958016466801761 2285938851718512350101321)
                      ·
                        rfl

theorem cell23_4451850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_4451850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451850 prefixEnd_4451850 := by exact prefixLift 4451850
  have htrace : WordTrace (prefixWord ++ tailWord_4451850) baseStart_4451850 baseEnd_4451850 := by
    simpa [prefixWord, tailWord_4451850, baseEnd_4451850] using wordTrace_append hprefix tailTrace_4451850
  have hstable : (prefixWord ++ tailWord_4451850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451850).length < 2 ^ (prefixWord ++ tailWord_4451850).sum := by decide
  have hdescent : baseEnd_4451850 < baseStart_4451850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451886 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4451886 : Nat := 118140960795 + 4451886 * 2 ^ 59
def prefixEnd_4451886 : Nat := 4983230072969 + 3 ^ 40 * 4451886 * 2
def baseEnd_4451886 : Nat := 761985779007358069750385

theorem tailTrace_4451886 : CollatzResearch.WordTrace tailWord_4451886 prefixEnd_4451886 761985779007358069750385 := by
  unfold tailWord_4451886
  simp only [CollatzResearch.WordTrace]
  refine ⟨20296702743698102305201939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108249081299723212294410341 20296702743698102305201939)
  ·
    refine ⟨30445054115547153457802909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20296702743698102305201939 30445054115547153457802909)
    ·
      refine ⟨11416895293330182546676091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30445054115547153457802909 11416895293330182546676091)
      ·
        refine ⟨17125342939995273820014137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11416895293330182546676091 17125342939995273820014137)
        ·
          refine ⟨12844007204996455365010603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17125342939995273820014137 12844007204996455365010603)
          ·
            refine ⟨19266010807494683047515905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12844007204996455365010603 19266010807494683047515905)
            ·
              refine ⟨14449508105621012285636929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19266010807494683047515905 14449508105621012285636929)
              ·
                refine ⟨10837131079215759214227697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14449508105621012285636929 10837131079215759214227697)
                ·
                  refine ⟨8127848309411819410670773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10837131079215759214227697 8127848309411819410670773)
                  ·
                    refine ⟨761985779007358069750385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8127848309411819410670773 761985779007358069750385)
                    ·
                      rfl

theorem cell23_4451886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4451886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451886 prefixEnd_4451886 := by exact prefixLift 4451886
  have htrace : WordTrace (prefixWord ++ tailWord_4451886) baseStart_4451886 baseEnd_4451886 := by
    simpa [prefixWord, tailWord_4451886, baseEnd_4451886] using wordTrace_append hprefix tailTrace_4451886
  have hstable : (prefixWord ++ tailWord_4451886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451886).length < 2 ^ (prefixWord ++ tailWord_4451886).sum := by decide
  have hdescent : baseEnd_4451886 < baseStart_4451886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451909 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_4451909 : Nat := 118140960795 + 4451909 * 2 ^ 59
def prefixEnd_4451909 : Nat := 4983230072969 + 3 ^ 40 * 4451909 * 2
def baseEnd_4451909 : Nat := 2285969147077127619263549

theorem tailTrace_4451909 : CollatzResearch.WordTrace tailWord_4451909 prefixEnd_4451909 2285969147077127619263549 := by
  unfold tailWord_4451909
  simp only [CollatzResearch.WordTrace]
  refine ⟨162374460828501493369702781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108249640552334328913135187 162374460828501493369702781)
  ·
    refine ⟨60890422810688060013638543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162374460828501493369702781 60890422810688060013638543)
    ·
      refine ⟨91335634216032090020457815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60890422810688060013638543 91335634216032090020457815)
      ·
        refine ⟨137003451324048135030686723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91335634216032090020457815 137003451324048135030686723)
        ·
          refine ⟨205505176986072202546030085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137003451324048135030686723 205505176986072202546030085)
          ·
            refine ⟨38532220684888537977380641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205505176986072202546030085 38532220684888537977380641)
            ·
              refine ⟨28899165513666403483035481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38532220684888537977380641 28899165513666403483035481)
              ·
                refine ⟨21674374135249802612276611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28899165513666403483035481 21674374135249802612276611)
                ·
                  refine ⟨32511561202874703918414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21674374135249802612276611 32511561202874703918414917)
                  ·
                    refine ⟨6095917725539006984702797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32511561202874703918414917 6095917725539006984702797)
                    ·
                      refine ⟨2285969147077127619263549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6095917725539006984702797 2285969147077127619263549)
                      ·
                        rfl

theorem cell23_4451909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_4451909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451909 prefixEnd_4451909 := by exact prefixLift 4451909
  have htrace : WordTrace (prefixWord ++ tailWord_4451909) baseStart_4451909 baseEnd_4451909 := by
    simpa [prefixWord, tailWord_4451909, baseEnd_4451909] using wordTrace_append hprefix tailTrace_4451909
  have hstable : (prefixWord ++ tailWord_4451909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451909).length < 2 ^ (prefixWord ++ tailWord_4451909).sum := by decide
  have hdescent : baseEnd_4451909 < baseStart_4451909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451912 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 12]
def baseStart_4451912 : Nat := 118140960795 + 4451912 * 2 ^ 59
def prefixEnd_4451912 : Nat := 4983230072969 + 3 ^ 40 * 4451912 * 2
def baseEnd_4451912 : Nat := 253996743057676789725115

theorem tailTrace_4451912 : CollatzResearch.WordTrace tailWord_4451912 prefixEnd_4451912 253996743057676789725115 := by
  unfold tailWord_4451912
  simp only [CollatzResearch.WordTrace]
  refine ⟨81187285123745312441030995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108249713498327083254707993 81187285123745312441030995)
  ·
    refine ⟨121780927685617968661546493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81187285123745312441030995 121780927685617968661546493)
    ·
      refine ⟨45667847882106738248079935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121780927685617968661546493 45667847882106738248079935)
      ·
        refine ⟨68501771823160107372119903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45667847882106738248079935 68501771823160107372119903)
        ·
          refine ⟨102752657734740161058179855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68501771823160107372119903 102752657734740161058179855)
          ·
            refine ⟨154128986602110241587269783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102752657734740161058179855 154128986602110241587269783)
            ·
              refine ⟨231193479903165362380904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154128986602110241587269783 231193479903165362380904675)
              ·
                refine ⟨346790219854748043571357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231193479903165362380904675 346790219854748043571357013)
                ·
                  refine ⟨253996743057676789725115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 346790219854748043571357013 253996743057676789725115)
                  ·
                    rfl

theorem cell23_4451912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_4451912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451912 prefixEnd_4451912 := by exact prefixLift 4451912
  have htrace : WordTrace (prefixWord ++ tailWord_4451912) baseStart_4451912 baseEnd_4451912 := by
    simpa [prefixWord, tailWord_4451912, baseEnd_4451912] using wordTrace_append hprefix tailTrace_4451912
  have hstable : (prefixWord ++ tailWord_4451912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451912).length < 2 ^ (prefixWord ++ tailWord_4451912).sum := by decide
  have hdescent : baseEnd_4451912 < baseStart_4451912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451916 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_4451916 : Nat := 118140960795 + 4451916 * 2 ^ 59
def prefixEnd_4451916 : Nat := 4983230072969 + 3 ^ 40 * 4451916 * 2
def baseEnd_4451916 : Nat := 761990913813903030625339

theorem tailTrace_4451916 : CollatzResearch.WordTrace tailWord_4451916 prefixEnd_4451916 761990913813903030625339 := by
  unfold tailWord_4451916
  simp only [CollatzResearch.WordTrace]
  refine ⟨81187358069738066782603801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108249810759650755710138401 81187358069738066782603801)
  ·
    refine ⟨60890518552303550086952851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81187358069738066782603801 60890518552303550086952851)
    ·
      refine ⟨91335777828455325130429277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60890518552303550086952851 91335777828455325130429277)
      ·
        refine ⟨34250916685670746923910979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91335777828455325130429277 34250916685670746923910979)
        ·
          refine ⟨51376375028506120385866469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34250916685670746923910979 51376375028506120385866469)
          ·
            refine ⟨9633070317844897572349963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51376375028506120385866469 9633070317844897572349963)
            ·
              refine ⟨14449605476767346358524945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633070317844897572349963 14449605476767346358524945)
              ·
                refine ⟨10837204107575509768893709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14449605476767346358524945 10837204107575509768893709)
                ·
                  refine ⟨4063951540340816163335141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10837204107575509768893709 4063951540340816163335141)
                  ·
                    refine ⟨761990913813903030625339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063951540340816163335141 761990913813903030625339)
                    ·
                      rfl

theorem cell23_4451916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_4451916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451916 prefixEnd_4451916 := by exact prefixLift 4451916
  have htrace : WordTrace (prefixWord ++ tailWord_4451916) baseStart_4451916 baseEnd_4451916 := by
    simpa [prefixWord, tailWord_4451916, baseEnd_4451916] using wordTrace_append hprefix tailTrace_4451916
  have hstable : (prefixWord ++ tailWord_4451916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451916).length < 2 ^ (prefixWord ++ tailWord_4451916).sum := by decide
  have hdescent : baseEnd_4451916 < baseStart_4451916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451946 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_4451946 : Nat := 118140960795 + 4451946 * 2 ^ 59
def prefixEnd_4451946 : Nat := 4983230072969 + 3 ^ 40 * 4451946 * 2
def baseEnd_4451946 : Nat := 253998682873482663833431

theorem tailTrace_4451946 : CollatzResearch.WordTrace tailWord_4451946 prefixEnd_4451946 253998682873482663833431 := by
  unfold tailWord_4451946
  simp only [CollatzResearch.WordTrace]
  refine ⟨40593952582341862172199923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108250540219578299125866461 40593952582341862172199923)
  ·
    refine ⟨60890928873512793258299885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40593952582341862172199923 60890928873512793258299885)
    ·
      refine ⟨22834098327567297471862457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60890928873512793258299885 22834098327567297471862457)
      ·
        refine ⟨17125573745675473103896843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22834098327567297471862457 17125573745675473103896843)
        ·
          refine ⟨25688360618513209655845265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17125573745675473103896843 25688360618513209655845265)
          ·
            refine ⟨19266270463884907241883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25688360618513209655845265 19266270463884907241883949)
            ·
              refine ⟨7224851423956840215706481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19266270463884907241883949 7224851423956840215706481)
              ·
                refine ⟨5418638567967630161779861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224851423956840215706481 5418638567967630161779861)
                ·
                  refine ⟨253998682873482663833431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5418638567967630161779861 253998682873482663833431)
                  ·
                    rfl

theorem cell23_4451946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_4451946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451946 prefixEnd_4451946 := by exact prefixLift 4451946
  have htrace : WordTrace (prefixWord ++ tailWord_4451946) baseStart_4451946 baseEnd_4451946 := by
    simpa [prefixWord, tailWord_4451946, baseEnd_4451946] using wordTrace_append hprefix tailTrace_4451946
  have hstable : (prefixWord ++ tailWord_4451946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451946).length < 2 ^ (prefixWord ++ tailWord_4451946).sum := by decide
  have hdescent : baseEnd_4451946 < baseStart_4451946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4451989 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_4451989 : Nat := 118140960795 + 4451989 * 2 ^ 59
def prefixEnd_4451989 : Nat := 4983230072969 + 3 ^ 40 * 4451989 * 2
def baseEnd_4451989 : Nat := 762003408509829102087727

theorem tailTrace_4451989 : CollatzResearch.WordTrace tailWord_4451989 prefixEnd_4451989 762003408509829102087727 := by
  unfold tailWord_4451989
  simp only [CollatzResearch.WordTrace]
  refine ⟨162377378668211667032615021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108251585778807778021743347 162377378668211667032615021)
  ·
    refine ⟨60891517000579375137230633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162377378668211667032615021 60891517000579375137230633)
    ·
      refine ⟨45668637750434531352922975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60891517000579375137230633 45668637750434531352922975)
      ·
        refine ⟨68502956625651797029384463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45668637750434531352922975 68502956625651797029384463)
        ·
          refine ⟨102754434938477695544076695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68502956625651797029384463 102754434938477695544076695)
          ·
            refine ⟨154131652407716543316115043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102754434938477695544076695 154131652407716543316115043)
            ·
              refine ⟨231197478611574814974172565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154131652407716543316115043 231197478611574814974172565)
              ·
                refine ⟨10837381809917569451914339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231197478611574814974172565 10837381809917569451914339)
                ·
                  refine ⟨16256072714876354177871509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10837381809917569451914339 16256072714876354177871509)
                  ·
                    refine ⟨762003408509829102087727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16256072714876354177871509 762003408509829102087727)
                    ·
                      rfl

theorem cell23_4451989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_4451989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4451989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4451989 prefixEnd_4451989 := by exact prefixLift 4451989
  have htrace : WordTrace (prefixWord ++ tailWord_4451989) baseStart_4451989 baseEnd_4451989 := by
    simpa [prefixWord, tailWord_4451989, baseEnd_4451989] using wordTrace_append hprefix tailTrace_4451989
  have hstable : (prefixWord ++ tailWord_4451989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4451989).length < 2 ^ (prefixWord ++ tailWord_4451989).sum := by decide
  have hdescent : baseEnd_4451989 < baseStart_4451989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4451989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452019 : List Nat := [1, 1, 1, 2, 3, 3, 4, 8]
def baseStart_4452019 : Nat := 118140960795 + 4452019 * 2 ^ 59
def prefixEnd_4452019 : Nat := 4983230072969 + 3 ^ 40 * 4452019 * 2
def baseEnd_4452019 : Nat := 84667615924041562551409

theorem tailTrace_4452019 : CollatzResearch.WordTrace tailWord_4452019 prefixEnd_4452019 84667615924041562551409 := by
  unfold tailWord_4452019
  simp only [CollatzResearch.WordTrace]
  refine ⟨162378472858102982156207111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108252315238735321437471407 162378472858102982156207111)
  ·
    refine ⟨243567709287154473234310667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162378472858102982156207111 243567709287154473234310667)
    ·
      refine ⟨365351563930731709851466001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243567709287154473234310667 365351563930731709851466001)
      ·
        refine ⟨274013672948048782388599501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365351563930731709851466001 274013672948048782388599501)
        ·
          refine ⟨102755127355518293395724813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274013672948048782388599501 102755127355518293395724813)
          ·
            refine ⟨38533172758319360023396805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102755127355518293395724813 38533172758319360023396805)
            ·
              refine ⟨7224969892184880004386901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38533172758319360023396805 7224969892184880004386901)
              ·
                refine ⟨84667615924041562551409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7224969892184880004386901 84667615924041562551409)
                ·
                  rfl

theorem cell23_4452019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 8].length) (baseStart_4452019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452019 prefixEnd_4452019 := by exact prefixLift 4452019
  have htrace : WordTrace (prefixWord ++ tailWord_4452019) baseStart_4452019 baseEnd_4452019 := by
    simpa [prefixWord, tailWord_4452019, baseEnd_4452019] using wordTrace_append hprefix tailTrace_4452019
  have hstable : (prefixWord ++ tailWord_4452019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452019).length < 2 ^ (prefixWord ++ tailWord_4452019).sum := by decide
  have hdescent : baseEnd_4452019 < baseStart_4452019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452023 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 2, 4]
def baseStart_4452023 : Nat := 118140960795 + 4452023 * 2 ^ 59
def prefixEnd_4452023 : Nat := 4983230072969 + 3 ^ 40 * 4452023 * 2
def baseEnd_4452023 : Nat := 762009227957246724412675

theorem tailTrace_4452023 : CollatzResearch.WordTrace tailWord_4452023 prefixEnd_4452023 762009227957246724412675 := by
  unfold tailWord_4452023
  simp only [CollatzResearch.WordTrace]
  refine ⟨162378618750088490839352723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108252412500058993892901815 162378618750088490839352723)
  ·
    refine ⟨243567928125132736259029085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162378618750088490839352723 243567928125132736259029085)
    ·
      refine ⟨91337973046924776097135907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243567928125132736259029085 91337973046924776097135907)
      ·
        refine ⟨137006959570387164145703861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91337973046924776097135907 137006959570387164145703861)
        ·
          refine ⟨12844402459723796638659737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137006959570387164145703861 12844402459723796638659737)
          ·
            refine ⟨9633301844792847478994803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12844402459723796638659737 9633301844792847478994803)
            ·
              refine ⟨14449952767189271218492205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633301844792847478994803 14449952767189271218492205)
              ·
                refine ⟨5418732287695976706934577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14449952767189271218492205 5418732287695976706934577)
                ·
                  refine ⟨4064049215771982530200933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418732287695976706934577 4064049215771982530200933)
                  ·
                    refine ⟨762009227957246724412675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064049215771982530200933 762009227957246724412675)
                    ·
                      rfl

theorem cell23_4452023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_4452023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452023 prefixEnd_4452023 := by exact prefixLift 4452023
  have htrace : WordTrace (prefixWord ++ tailWord_4452023) baseStart_4452023 baseEnd_4452023 := by
    simpa [prefixWord, tailWord_4452023, baseEnd_4452023] using wordTrace_append hprefix tailTrace_4452023
  have hstable : (prefixWord ++ tailWord_4452023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452023).length < 2 ^ (prefixWord ++ tailWord_4452023).sum := by decide
  have hdescent : baseEnd_4452023 < baseStart_4452023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452030 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_4452030 : Nat := 118140960795 + 4452030 * 2 ^ 59
def prefixEnd_4452030 : Nat := 4983230072969 + 3 ^ 40 * 4452030 * 2
def baseEnd_4452030 : Nat := 2286031278236321645850493

theorem tailTrace_4452030 : CollatzResearch.WordTrace tailWord_4452030 prefixEnd_4452030 2286031278236321645850493 := by
  unfold tailWord_4452030
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297359257632891379357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108252582707375420689905029 20297359257632891379357193)
  ·
    refine ⟨15223019443224668534517895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20297359257632891379357193 15223019443224668534517895)
    ·
      refine ⟨22834529164837002801776843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15223019443224668534517895 22834529164837002801776843)
      ·
        refine ⟨34251793747255504202665265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22834529164837002801776843 34251793747255504202665265)
        ·
          refine ⟨25688845310441628151998949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34251793747255504202665265 25688845310441628151998949)
          ·
            refine ⟨4816658495707805278499803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25688845310441628151998949 4816658495707805278499803)
            ·
              refine ⟨7224987743561707917749705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816658495707805278499803 7224987743561707917749705)
              ·
                refine ⟨5418740807671280938312279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224987743561707917749705 5418740807671280938312279)
                ·
                  refine ⟨8128111211506921407468419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418740807671280938312279 8128111211506921407468419)
                  ·
                    refine ⟨12192166817260382111202629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8128111211506921407468419 12192166817260382111202629)
                    ·
                      refine ⟨2286031278236321645850493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12192166817260382111202629 2286031278236321645850493)
                      ·
                        rfl

theorem cell23_4452030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_4452030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452030 prefixEnd_4452030 := by exact prefixLift 4452030
  have htrace : WordTrace (prefixWord ++ tailWord_4452030) baseStart_4452030 baseEnd_4452030 := by
    simpa [prefixWord, tailWord_4452030, baseEnd_4452030] using wordTrace_append hprefix tailTrace_4452030
  have hstable : (prefixWord ++ tailWord_4452030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452030).length < 2 ^ (prefixWord ++ tailWord_4452030).sum := by decide
  have hdescent : baseEnd_4452030 < baseStart_4452030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452114 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4452114 : Nat := 118140960795 + 4452114 * 2 ^ 59
def prefixEnd_4452114 : Nat := 4983230072969 + 3 ^ 40 * 4452114 * 2
def baseEnd_4452114 : Nat := 2286074410611299317200107

theorem tailTrace_4452114 : CollatzResearch.WordTrace tailWord_4452114 prefixEnd_4452114 2286074410611299317200107 := by
  unfold tailWord_4452114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40595484448189703345228849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108254625195172542253943597 40595484448189703345228849)
  ·
    refine ⟨30446613336142277508921637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40595484448189703345228849 30446613336142277508921637)
    ·
      refine ⟨5708740000526677032922807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30446613336142277508921637 5708740000526677032922807)
      ·
        refine ⟨8563110000790015549384211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5708740000526677032922807 8563110000790015549384211)
        ·
          refine ⟨12844665001185023324076317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563110000790015549384211 12844665001185023324076317)
          ·
            refine ⟨4816749375444383746528619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12844665001185023324076317 4816749375444383746528619)
            ·
              refine ⟨7225124063166575619792929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816749375444383746528619 7225124063166575619792929)
              ·
                refine ⟨5418843047374931714844697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225124063166575619792929 5418843047374931714844697)
                ·
                  refine ⟨4064132285531198786133523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418843047374931714844697 4064132285531198786133523)
                  ·
                    refine ⟨6096198428296798179200285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4064132285531198786133523 6096198428296798179200285)
                    ·
                      refine ⟨2286074410611299317200107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096198428296798179200285 2286074410611299317200107)
                      ·
                        rfl

theorem cell23_4452114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4452114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452114 prefixEnd_4452114 := by exact prefixLift 4452114
  have htrace : WordTrace (prefixWord ++ tailWord_4452114) baseStart_4452114 baseEnd_4452114 := by
    simpa [prefixWord, tailWord_4452114, baseEnd_4452114] using wordTrace_append hprefix tailTrace_4452114
  have hstable : (prefixWord ++ tailWord_4452114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452114).length < 2 ^ (prefixWord ++ tailWord_4452114).sum := by decide
  have hdescent : baseEnd_4452114 < baseStart_4452114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452156 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_4452156 : Nat := 118140960795 + 4452156 * 2 ^ 59
def prefixEnd_4452156 : Nat := 4983230072969 + 3 ^ 40 * 4452156 * 2
def baseEnd_4452156 : Nat := 762031992266262717624971

theorem tailTrace_4452156 : CollatzResearch.WordTrace tailWord_4452156 prefixEnd_4452156 762031992266262717624971 := by
  unfold tailWord_4452156
  simp only [CollatzResearch.WordTrace]
  refine ⟨81191734829303327276972161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108255646439071103035962881 81191734829303327276972161)
  ·
    refine ⟨60893801121977495457729121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81191734829303327276972161 60893801121977495457729121)
    ·
      refine ⟨45670350841483121593296841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60893801121977495457729121 45670350841483121593296841)
      ·
        refine ⟨34252763131112341194972631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45670350841483121593296841 34252763131112341194972631)
        ·
          refine ⟨51379144696668511792458947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34252763131112341194972631 51379144696668511792458947)
          ·
            refine ⟨77068717045002767688688421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51379144696668511792458947 77068717045002767688688421)
            ·
              refine ⟨14450384445938018941629079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77068717045002767688688421 14450384445938018941629079)
              ·
                refine ⟨21675576668907028412443619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14450384445938018941629079 21675576668907028412443619)
                ·
                  refine ⟨32513365003360542618665429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21675576668907028412443619 32513365003360542618665429)
                  ·
                    refine ⟨762031992266262717624971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32513365003360542618665429 762031992266262717624971)
                    ·
                      rfl

theorem cell23_4452156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_4452156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452156 prefixEnd_4452156 := by exact prefixLift 4452156
  have htrace : WordTrace (prefixWord ++ tailWord_4452156) baseStart_4452156 baseEnd_4452156 := by
    simpa [prefixWord, tailWord_4452156, baseEnd_4452156] using wordTrace_append hprefix tailTrace_4452156
  have hstable : (prefixWord ++ tailWord_4452156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452156).length < 2 ^ (prefixWord ++ tailWord_4452156).sum := by decide
  have hdescent : baseEnd_4452156 < baseStart_4452156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452183 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_4452183 : Nat := 118140960795 + 4452183 * 2 ^ 59
def prefixEnd_4452183 : Nat := 4983230072969 + 3 ^ 40 * 4452183 * 2
def baseEnd_4452183 : Nat := 2286109840776459547237289

theorem tailTrace_4452183 : CollatzResearch.WordTrace tailWord_4452183 prefixEnd_4452183 2286109840776459547237289 := by
  unfold tailWord_4452183
  simp only [CollatzResearch.WordTrace]
  refine ⟨162384454429508838165177203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108256302953005892110118135 162384454429508838165177203)
  ·
    refine ⟨243576681644263257247765805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162384454429508838165177203 243576681644263257247765805)
    ·
      refine ⟨91341255616598721467912177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243576681644263257247765805 91341255616598721467912177)
      ·
        refine ⟨68505941712449041100934133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91341255616598721467912177 68505941712449041100934133)
        ·
          refine ⟨6422432035542097603212575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68505941712449041100934133 6422432035542097603212575)
          ·
            refine ⟨9633648053313146404818863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422432035542097603212575 9633648053313146404818863)
            ·
              refine ⟨14450472079969719607228295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633648053313146404818863 14450472079969719607228295)
              ·
                refine ⟨21675708119954579410842443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14450472079969719607228295 21675708119954579410842443)
                ·
                  refine ⟨32513562179931869116263665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21675708119954579410842443 32513562179931869116263665)
                  ·
                    refine ⟨24385171634948901837197749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32513562179931869116263665 24385171634948901837197749)
                    ·
                      refine ⟨2286109840776459547237289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24385171634948901837197749 2286109840776459547237289)
                      ·
                        rfl

theorem cell23_4452183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_4452183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452183 prefixEnd_4452183 := by exact prefixLift 4452183
  have htrace : WordTrace (prefixWord ++ tailWord_4452183) baseStart_4452183 baseEnd_4452183 := by
    simpa [prefixWord, tailWord_4452183, baseEnd_4452183] using wordTrace_append hprefix tailTrace_4452183
  have hstable : (prefixWord ++ tailWord_4452183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452183).length < 2 ^ (prefixWord ++ tailWord_4452183).sum := by decide
  have hdescent : baseEnd_4452183 < baseStart_4452183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452188 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4452188 : Nat := 118140960795 + 4452188 * 2 ^ 59
def prefixEnd_4452188 : Nat := 4983230072969 + 3 ^ 40 * 4452188 * 2
def baseEnd_4452188 : Nat := 2286112408179732027674767

theorem tailTrace_4452188 : CollatzResearch.WordTrace tailWord_4452188 prefixEnd_4452188 2286112408179732027674767 := by
  unfold tailWord_4452188
  simp only [CollatzResearch.WordTrace]
  refine ⟨81192318397245362009554609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108256424529660482679406145 81192318397245362009554609)
  ·
    refine ⟨60894238797934021507165957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81192318397245362009554609 60894238797934021507165957)
    ·
      refine ⟨11417669774612629032593617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60894238797934021507165957 11417669774612629032593617)
      ·
        refine ⟨8563252330959471774445213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11417669774612629032593617 8563252330959471774445213)
        ·
          refine ⟨3211219624109801915416955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8563252330959471774445213 3211219624109801915416955)
          ·
            refine ⟨4816829436164702873125433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211219624109801915416955 4816829436164702873125433)
            ·
              refine ⟨3612622077123527154844075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816829436164702873125433 3612622077123527154844075)
              ·
                refine ⟨5418933115685290732266113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612622077123527154844075 5418933115685290732266113)
                ·
                  refine ⟨4064199836763968049199585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418933115685290732266113 4064199836763968049199585)
                  ·
                    refine ⟨3048149877572976036899689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4064199836763968049199585 3048149877572976036899689)
                    ·
                      refine ⟨2286112408179732027674767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048149877572976036899689 2286112408179732027674767)
                      ·
                        rfl

theorem cell23_4452188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4452188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452188 prefixEnd_4452188 := by exact prefixLift 4452188
  have htrace : WordTrace (prefixWord ++ tailWord_4452188) baseStart_4452188 baseEnd_4452188 := by
    simpa [prefixWord, tailWord_4452188, baseEnd_4452188] using wordTrace_append hprefix tailTrace_4452188
  have hstable : (prefixWord ++ tailWord_4452188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452188).length < 2 ^ (prefixWord ++ tailWord_4452188).sum := by decide
  have hdescent : baseEnd_4452188 < baseStart_4452188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452193 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_4452193 : Nat := 118140960795 + 4452193 * 2 ^ 59
def prefixEnd_4452193 : Nat := 4983230072969 + 3 ^ 40 * 4452193 * 2
def baseEnd_4452193 : Nat := 2286114975583004508112243

theorem tailTrace_4452193 : CollatzResearch.WordTrace tailWord_4452193 prefixEnd_4452193 2286114975583004508112243 := by
  unfold tailWord_4452193
  simp only [CollatzResearch.WordTrace]
  refine ⟨162384819159472609873041233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108256546106315073248694155 162384819159472609873041233)
  ·
    refine ⟨121788614369604457404780925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162384819159472609873041233 121788614369604457404780925)
    ·
      refine ⟨45670730388601671526792847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121788614369604457404780925 45670730388601671526792847)
      ·
        refine ⟨68506095582902507290189271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45670730388601671526792847 68506095582902507290189271)
        ·
          refine ⟨102759143374353760935283907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68506095582902507290189271 102759143374353760935283907)
          ·
            refine ⟨154138715061530641402925861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102759143374353760935283907 154138715061530641402925861)
            ·
              refine ⟨28901009074036995263048599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154138715061530641402925861 28901009074036995263048599)
              ·
                refine ⟨43351513611055492894572899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28901009074036995263048599 43351513611055492894572899)
                ·
                  refine ⟨65027270416583239341859349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43351513611055492894572899 65027270416583239341859349)
                  ·
                    refine ⟨3048153300777339344149657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65027270416583239341859349 3048153300777339344149657)
                    ·
                      refine ⟨2286114975583004508112243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048153300777339344149657 2286114975583004508112243)
                      ·
                        rfl

theorem cell23_4452193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_4452193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452193 prefixEnd_4452193 := by exact prefixLift 4452193
  have htrace : WordTrace (prefixWord ++ tailWord_4452193) baseStart_4452193 baseEnd_4452193 := by
    simpa [prefixWord, tailWord_4452193, baseEnd_4452193] using wordTrace_append hprefix tailTrace_4452193
  have hstable : (prefixWord ++ tailWord_4452193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452193).length < 2 ^ (prefixWord ++ tailWord_4452193).sum := by decide
  have hdescent : baseEnd_4452193 < baseStart_4452193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452233 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 6]
def baseStart_4452233 : Nat := 118140960795 + 4452233 * 2 ^ 59
def prefixEnd_4452233 : Nat := 4983230072969 + 3 ^ 40 * 4452233 * 2
def baseEnd_4452233 : Nat := 254015057201020483512451

theorem tailTrace_4452233 : CollatzResearch.WordTrace tailWord_4452233 prefixEnd_4452233 254015057201020483512451 := by
  unfold tailWord_4452233
  simp only [CollatzResearch.WordTrace]
  refine ⟨162386278079327696704497353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108257518719551797802998235 162386278079327696704497353)
  ·
    refine ⟨121789708559495772528373015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162386278079327696704497353 121789708559495772528373015)
    ·
      refine ⟨182684562839243658792559523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121789708559495772528373015 182684562839243658792559523)
      ·
        refine ⟨274026844258865488188839285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182684562839243658792559523 274026844258865488188839285)
        ·
          refine ⟨25690016649268639517703683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274026844258865488188839285 25690016649268639517703683)
          ·
            refine ⟨38535024973902959276555525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25690016649268639517703683 38535024973902959276555525)
            ·
              refine ⟨7225317182606804864354161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38535024973902959276555525 7225317182606804864354161)
              ·
                refine ⟨5418987886955103648265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225317182606804864354161 5418987886955103648265621)
                ·
                  refine ⟨254015057201020483512451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5418987886955103648265621 254015057201020483512451)
                  ·
                    rfl

theorem cell23_4452233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_4452233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452233 prefixEnd_4452233 := by exact prefixLift 4452233
  have htrace : WordTrace (prefixWord ++ tailWord_4452233) baseStart_4452233 baseEnd_4452233 := by
    simpa [prefixWord, tailWord_4452233, baseEnd_4452233] using wordTrace_append hprefix tailTrace_4452233
  have hstable : (prefixWord ++ tailWord_4452233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452233).length < 2 ^ (prefixWord ++ tailWord_4452233).sum := by decide
  have hdescent : baseEnd_4452233 < baseStart_4452233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452236 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4452236 : Nat := 118140960795 + 4452236 * 2 ^ 59
def prefixEnd_4452236 : Nat := 4983230072969 + 3 ^ 40 * 4452236 * 2
def baseEnd_4452236 : Nat := 2286137055251147839874545

theorem tailTrace_4452236 : CollatzResearch.WordTrace tailWord_4452236 prefixEnd_4452236 2286137055251147839874545 := by
  unfold tailWord_4452236
  simp only [CollatzResearch.WordTrace]
  refine ⟨81193193749158414108428281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108257591665544552144571041 81193193749158414108428281)
  ·
    refine ⟨60894895311868810581321211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81193193749158414108428281 60894895311868810581321211)
    ·
      refine ⟨91342342967803215871981817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60894895311868810581321211 91342342967803215871981817)
      ·
        refine ⟨68506757225852411903986363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91342342967803215871981817 68506757225852411903986363)
        ·
          refine ⟨102760135838778617855979545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68506757225852411903986363 102760135838778617855979545)
          ·
            refine ⟨77070101879083963391984659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102760135838778617855979545 77070101879083963391984659)
            ·
              refine ⟨115605152818625945087976989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77070101879083963391984659 115605152818625945087976989)
              ·
                refine ⟨43351932306984729407991371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115605152818625945087976989 43351932306984729407991371)
                ·
                  refine ⟨65027898460477094111987057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43351932306984729407991371 65027898460477094111987057)
                  ·
                    refine ⟨48770923845357820583990293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65027898460477094111987057 48770923845357820583990293)
                    ·
                      refine ⟨2286137055251147839874545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48770923845357820583990293 2286137055251147839874545)
                      ·
                        rfl

theorem cell23_4452236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4452236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452236 prefixEnd_4452236 := by exact prefixLift 4452236
  have htrace : WordTrace (prefixWord ++ tailWord_4452236) baseStart_4452236 baseEnd_4452236 := by
    simpa [prefixWord, tailWord_4452236, baseEnd_4452236] using wordTrace_append hprefix tailTrace_4452236
  have hstable : (prefixWord ++ tailWord_4452236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452236).length < 2 ^ (prefixWord ++ tailWord_4452236).sum := by decide
  have hdescent : baseEnd_4452236 < baseStart_4452236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452254 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4452254 : Nat := 118140960795 + 4452254 * 2 ^ 59
def prefixEnd_4452254 : Nat := 4983230072969 + 3 ^ 40 * 4452254 * 2
def baseEnd_4452254 : Nat := 762048765967642923149821

theorem tailTrace_4452254 : CollatzResearch.WordTrace tailWord_4452254 prefixEnd_4452254 762048765967642923149821 := by
  unfold tailWord_4452254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298380501531452161376477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108258029341501078194007877 20298380501531452161376477)
  ·
    refine ⟨7611892688074294560516179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20298380501531452161376477 7611892688074294560516179)
    ·
      refine ⟨11417839032111441840774269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7611892688074294560516179 11417839032111441840774269)
      ·
        refine ⟨4281689637041790690290351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11417839032111441840774269 4281689637041790690290351)
        ·
          refine ⟨6422534455562686035435527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281689637041790690290351 6422534455562686035435527)
          ·
            refine ⟨9633801683344029053153291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422534455562686035435527 9633801683344029053153291)
            ·
              refine ⟨14450702525016043579729937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633801683344029053153291 14450702525016043579729937)
              ·
                refine ⟨10838026893762032684797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14450702525016043579729937 10838026893762032684797453)
                ·
                  refine ⟨4064260085160762256799045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10838026893762032684797453 4064260085160762256799045)
                  ·
                    refine ⟨762048765967642923149821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064260085160762256799045 762048765967642923149821)
                    ·
                      rfl

theorem cell23_4452254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4452254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452254 prefixEnd_4452254 := by exact prefixLift 4452254
  have htrace : WordTrace (prefixWord ++ tailWord_4452254) baseStart_4452254 baseEnd_4452254 := by
    simpa [prefixWord, tailWord_4452254, baseEnd_4452254] using wordTrace_append hprefix tailTrace_4452254
  have hstable : (prefixWord ++ tailWord_4452254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452254).length < 2 ^ (prefixWord ++ tailWord_4452254).sum := by decide
  have hdescent : baseEnd_4452254 < baseStart_4452254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452256 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4452256 : Nat := 118140960795 + 4452256 * 2 ^ 59
def prefixEnd_4452256 : Nat := 4983230072969 + 3 ^ 40 * 4452256 * 2
def baseEnd_4452256 : Nat := 2286147324864237761624453

theorem tailTrace_4452256 : CollatzResearch.WordTrace tailWord_4452256 prefixEnd_4452256 2286147324864237761624453 := by
  unfold tailWord_4452256
  simp only [CollatzResearch.WordTrace]
  refine ⟨81193558479122185816292311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108258077972162914421723081 81193558479122185816292311)
  ·
    refine ⟨121790337718683278724438467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81193558479122185816292311 121790337718683278724438467)
    ·
      refine ⟨182685506578024918086657701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121790337718683278724438467 182685506578024918086657701)
      ·
        refine ⟨34253532483379672141248319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182685506578024918086657701 34253532483379672141248319)
        ·
          refine ⟨51380298725069508211872479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34253532483379672141248319 51380298725069508211872479)
          ·
            refine ⟨77070448087604262317808719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51380298725069508211872479 77070448087604262317808719)
            ·
              refine ⟨115605672131406393476713079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77070448087604262317808719 115605672131406393476713079)
              ·
                refine ⟨173408508197109590215069619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115605672131406393476713079 173408508197109590215069619)
                ·
                  refine ⟨260112762295664385322604429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173408508197109590215069619 260112762295664385322604429)
                  ·
                    refine ⟨97542285860874144495976661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260112762295664385322604429 97542285860874144495976661)
                    ·
                      refine ⟨2286147324864237761624453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97542285860874144495976661 2286147324864237761624453)
                      ·
                        rfl

theorem cell23_4452256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4452256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452256 prefixEnd_4452256 := by exact prefixLift 4452256
  have htrace : WordTrace (prefixWord ++ tailWord_4452256) baseStart_4452256 baseEnd_4452256 := by
    simpa [prefixWord, tailWord_4452256, baseEnd_4452256] using wordTrace_append hprefix tailTrace_4452256
  have hstable : (prefixWord ++ tailWord_4452256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452256).length < 2 ^ (prefixWord ++ tailWord_4452256).sum := by decide
  have hdescent : baseEnd_4452256 < baseStart_4452256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452260 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_4452260 : Nat := 118140960795 + 4452260 * 2 ^ 59
def prefixEnd_4452260 : Nat := 4983230072969 + 3 ^ 40 * 4452260 * 2
def baseEnd_4452260 : Nat := 2286149378786855745974435

theorem tailTrace_4452260 : CollatzResearch.WordTrace tailWord_4452260 prefixEnd_4452260 2286149378786855745974435 := by
  unfold tailWord_4452260
  simp only [CollatzResearch.WordTrace]
  refine ⟨81193631425114940157865117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108258175233486586877153489 81193631425114940157865117)
  ·
    refine ⟨30447611784418102559199419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81193631425114940157865117 30447611784418102559199419)
    ·
      refine ⟨45671417676627153838799129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30447611784418102559199419 45671417676627153838799129)
      ·
        refine ⟨34253563257470365379099347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45671417676627153838799129 34253563257470365379099347)
        ·
          refine ⟨51380344886205548068649021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34253563257470365379099347 51380344886205548068649021)
          ·
            refine ⟨19267629332327080525743383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51380344886205548068649021 19267629332327080525743383)
            ·
              refine ⟨28901443998490620788615075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19267629332327080525743383 28901443998490620788615075)
              ·
                refine ⟨43352165997735931182922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28901443998490620788615075 43352165997735931182922613)
                ·
                  refine ⟨4064265562287743548398995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43352165997735931182922613 4064265562287743548398995)
                  ·
                    refine ⟨6096398343431615322598493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4064265562287743548398995 6096398343431615322598493)
                    ·
                      refine ⟨2286149378786855745974435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096398343431615322598493 2286149378786855745974435)
                      ·
                        rfl

theorem cell23_4452260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_4452260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452260 prefixEnd_4452260 := by exact prefixLift 4452260
  have htrace : WordTrace (prefixWord ++ tailWord_4452260) baseStart_4452260 baseEnd_4452260 := by
    simpa [prefixWord, tailWord_4452260, baseEnd_4452260] using wordTrace_append hprefix tailTrace_4452260
  have hstable : (prefixWord ++ tailWord_4452260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452260).length < 2 ^ (prefixWord ++ tailWord_4452260).sum := by decide
  have hdescent : baseEnd_4452260 < baseStart_4452260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452284 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 6]
def baseStart_4452284 : Nat := 118140960795 + 4452284 * 2 ^ 59
def prefixEnd_4452284 : Nat := 4983230072969 + 3 ^ 40 * 4452284 * 2
def baseEnd_4452284 : Nat := 254017966924729294674925

theorem tailTrace_4452284 : CollatzResearch.WordTrace tailWord_4452284 prefixEnd_4452284 254017966924729294674925 := by
  unfold tailWord_4452284
  simp only [CollatzResearch.WordTrace]
  refine ⟨81194069101071466207301953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108258758801428621609735937 81194069101071466207301953)
  ·
    refine ⟨60895551825803599655476465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81194069101071466207301953 60895551825803599655476465)
    ·
      refine ⟨45671663869352699741607349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60895551825803599655476465 45671663869352699741607349)
      ·
        refine ⟨4281718487751815600775689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45671663869352699741607349 4281718487751815600775689)
        ·
          refine ⟨3211288865813861700581767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4281718487751815600775689 3211288865813861700581767)
          ·
            refine ⟨4816933298720792550872651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211288865813861700581767 4816933298720792550872651)
            ·
              refine ⟨7225399948081188826308977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816933298720792550872651 7225399948081188826308977)
              ·
                refine ⟨5419049961060891619731733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225399948081188826308977 5419049961060891619731733)
                ·
                  refine ⟨254017966924729294674925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5419049961060891619731733 254017966924729294674925)
                  ·
                    rfl

theorem cell23_4452284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_4452284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452284 prefixEnd_4452284 := by exact prefixLift 4452284
  have htrace : WordTrace (prefixWord ++ tailWord_4452284) baseStart_4452284 baseEnd_4452284 := by
    simpa [prefixWord, tailWord_4452284, baseEnd_4452284] using wordTrace_append hprefix tailTrace_4452284
  have hstable : (prefixWord ++ tailWord_4452284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452284).length < 2 ^ (prefixWord ++ tailWord_4452284).sum := by decide
  have hdescent : baseEnd_4452284 < baseStart_4452284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452303 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_4452303 : Nat := 118140960795 + 4452303 * 2 ^ 59
def prefixEnd_4452303 : Nat := 4983230072969 + 3 ^ 40 * 4452303 * 2
def baseEnd_4452303 : Nat := 2286171458454999077736737

theorem tailTrace_4452303 : CollatzResearch.WordTrace tailWord_4452303 prefixEnd_4452303 2286171458454999077736737 := by
  unfold tailWord_4452303
  simp only [CollatzResearch.WordTrace]
  refine ⟨162388831189074098659545563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108259220792716065773030375 162388831189074098659545563)
  ·
    refine ⟨243583246783611147989318345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162388831189074098659545563 243583246783611147989318345)
    ·
      refine ⟨182687435087708360991988759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243583246783611147989318345 182687435087708360991988759)
      ·
        refine ⟨274031152631562541487983139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182687435087708360991988759 274031152631562541487983139)
        ·
          refine ⟨411046728947343812231974709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274031152631562541487983139 411046728947343812231974709)
          ·
            refine ⟨38535630838813482396747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 411046728947343812231974709 38535630838813482396747629)
            ·
              refine ⟨14450861564555055898780361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38535630838813482396747629 14450861564555055898780361)
              ·
                refine ⟨10838146173416291924085271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14450861564555055898780361 10838146173416291924085271)
                ·
                  refine ⟨16257219260124437886127907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10838146173416291924085271 16257219260124437886127907)
                  ·
                    refine ⟨24385828890186656829191861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16257219260124437886127907 24385828890186656829191861)
                    ·
                      refine ⟨2286171458454999077736737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24385828890186656829191861 2286171458454999077736737)
                      ·
                        rfl

theorem cell23_4452303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_4452303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452303 prefixEnd_4452303 := by exact prefixLift 4452303
  have htrace : WordTrace (prefixWord ++ tailWord_4452303) baseStart_4452303 baseEnd_4452303 := by
    simpa [prefixWord, tailWord_4452303, baseEnd_4452303] using wordTrace_append hprefix tailTrace_4452303
  have hstable : (prefixWord ++ tailWord_4452303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452303).length < 2 ^ (prefixWord ++ tailWord_4452303).sum := by decide
  have hdescent : baseEnd_4452303 < baseStart_4452303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452323 : List Nat := [1, 1, 1, 6, 1, 3, 1, 9]
def baseStart_4452323 : Nat := 118140960795 + 4452323 * 2 ^ 59
def prefixEnd_4452323 : Nat := 4983230072969 + 3 ^ 40 * 4452323 * 2
def baseEnd_4452323 : Nat := 84673397335855148129135

theorem tailTrace_4452323 : CollatzResearch.WordTrace tailWord_4452323 prefixEnd_4452323 84673397335855148129135 := by
  unfold tailWord_4452323
  simp only [CollatzResearch.WordTrace]
  refine ⟨162389560649001642075273623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108259707099334428050182415 162389560649001642075273623)
  ·
    refine ⟨243584340973502463112910435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162389560649001642075273623 243584340973502463112910435)
    ·
      refine ⟨365376511460253694669365653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243584340973502463112910435 365376511460253694669365653)
      ·
        refine ⟨17127023974699391937626515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 365376511460253694669365653 17127023974699391937626515)
        ·
          refine ⟨25690535962049087906439773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17127023974699391937626515 25690535962049087906439773)
          ·
            refine ⟨9633950985768407964914915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25690535962049087906439773 9633950985768407964914915)
            ·
              refine ⟨14450926478652611947372373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633950985768407964914915 14450926478652611947372373)
              ·
                refine ⟨84673397335855148129135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14450926478652611947372373 84673397335855148129135)
                ·
                  rfl

theorem cell23_4452323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 9].length) (baseStart_4452323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452323 prefixEnd_4452323 := by exact prefixLift 4452323
  have htrace : WordTrace (prefixWord ++ tailWord_4452323) baseStart_4452323 baseEnd_4452323 := by
    simpa [prefixWord, tailWord_4452323, baseEnd_4452323] using wordTrace_append hprefix tailTrace_4452323
  have hstable : (prefixWord ++ tailWord_4452323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452323).length < 2 ^ (prefixWord ++ tailWord_4452323).sum := by decide
  have hdescent : baseEnd_4452323 < baseStart_4452323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452353 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4452353 : Nat := 118140960795 + 4452353 * 2 ^ 59
def prefixEnd_4452353 : Nat := 4983230072969 + 3 ^ 40 * 4452353 * 2
def baseEnd_4452353 : Nat := 762065710829241294037169

theorem tailTrace_4452353 : CollatzResearch.WordTrace tailWord_4452353 prefixEnd_4452353 762065710829241294037169 := by
  unfold tailWord_4452353
  simp only [CollatzResearch.WordTrace]
  refine ⟨162390654838892957198865713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108260436559261971465910475 162390654838892957198865713)
  ·
    refine ⟨121792991129169717899149285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162390654838892957198865713 121792991129169717899149285)
    ·
      refine ⟨22836185836719322106090491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121792991129169717899149285 22836185836719322106090491)
      ·
        refine ⟨34254278755078983159135737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22836185836719322106090491 34254278755078983159135737)
        ·
          refine ⟨25690709066309237369351803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34254278755078983159135737 25690709066309237369351803)
          ·
            refine ⟨38536063599463856054027705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25690709066309237369351803 38536063599463856054027705)
            ·
              refine ⟨28902047699597892040520779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38536063599463856054027705 28902047699597892040520779)
              ·
                refine ⟨43353071549396838060781169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28902047699597892040520779 43353071549396838060781169)
                ·
                  refine ⟨32514803662047628545585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43353071549396838060781169 32514803662047628545585877)
                  ·
                    refine ⟨762065710829241294037169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32514803662047628545585877 762065710829241294037169)
                    ·
                      rfl

theorem cell23_4452353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4452353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452353 prefixEnd_4452353 := by exact prefixLift 4452353
  have htrace : WordTrace (prefixWord ++ tailWord_4452353) baseStart_4452353 baseEnd_4452353 := by
    simpa [prefixWord, tailWord_4452353, baseEnd_4452353] using wordTrace_append hprefix tailTrace_4452353
  have hstable : (prefixWord ++ tailWord_4452353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452353).length < 2 ^ (prefixWord ++ tailWord_4452353).sum := by decide
  have hdescent : baseEnd_4452353 < baseStart_4452353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452407 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_4452407 : Nat := 118140960795 + 4452407 * 2 ^ 59
def prefixEnd_4452407 : Nat := 4983230072969 + 3 ^ 40 * 4452407 * 2
def baseEnd_4452407 : Nat := 2286224860443066670836259

theorem tailTrace_4452407 : CollatzResearch.WordTrace tailWord_4452407 prefixEnd_4452407 2286224860443066670836259 := by
  unfold tailWord_4452407
  simp only [CollatzResearch.WordTrace]
  refine ⟨162392624380697324421331475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108261749587131549614220983 162392624380697324421331475)
  ·
    refine ⟨243588936571045986631997213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162392624380697324421331475 243588936571045986631997213)
    ·
      refine ⟨91345851214142244986998955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243588936571045986631997213 91345851214142244986998955)
      ·
        refine ⟨137018776821213367480498433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91345851214142244986998955 137018776821213367480498433)
        ·
          refine ⟨102764082615910025610373825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137018776821213367480498433 102764082615910025610373825)
          ·
            refine ⟨77073061961932519207780369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102764082615910025610373825 77073061961932519207780369)
            ·
              refine ⟨57804796471449389405835277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77073061961932519207780369 57804796471449389405835277)
              ·
                refine ⟨21676798676793521027188229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57804796471449389405835277 21676798676793521027188229)
                ·
                  refine ⟨4064399751898785192597793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21676798676793521027188229 4064399751898785192597793)
                  ·
                    refine ⟨3048299813924088894448345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4064399751898785192597793 3048299813924088894448345)
                    ·
                      refine ⟨2286224860443066670836259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048299813924088894448345 2286224860443066670836259)
                      ·
                        rfl

theorem cell23_4452407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_4452407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452407 prefixEnd_4452407 := by exact prefixLift 4452407
  have htrace : WordTrace (prefixWord ++ tailWord_4452407) baseStart_4452407 baseEnd_4452407 := by
    simpa [prefixWord, tailWord_4452407, baseEnd_4452407] using wordTrace_append hprefix tailTrace_4452407
  have hstable : (prefixWord ++ tailWord_4452407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452407).length < 2 ^ (prefixWord ++ tailWord_4452407).sum := by decide
  have hdescent : baseEnd_4452407 < baseStart_4452407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452430 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_4452430 : Nat := 118140960795 + 4452430 * 2 ^ 59
def prefixEnd_4452430 : Nat := 4983230072969 + 3 ^ 40 * 4452430 * 2
def baseEnd_4452430 : Nat := 254026296722013342316517

theorem tailTrace_4452430 : CollatzResearch.WordTrace tailWord_4452430 prefixEnd_4452430 254026296722013342316517 := by
  unfold tailWord_4452430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20299182907451749918677343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108262308839742666232945829 20299182907451749918677343)
  ·
    refine ⟨30448774361177624878016015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20299182907451749918677343 30448774361177624878016015)
    ·
      refine ⟨45673161541766437317024023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30448774361177624878016015 45673161541766437317024023)
      ·
        refine ⟨68509742312649655975536035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45673161541766437317024023 68509742312649655975536035)
        ·
          refine ⟨102764613468974483963304053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68509742312649655975536035 102764613468974483963304053)
          ·
            refine ⟨9634182512716357871559755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102764613468974483963304053 9634182512716357871559755)
            ·
              refine ⟨14451273769074536807339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634182512716357871559755 14451273769074536807339633)
              ·
                refine ⟨10838455326805902605504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14451273769074536807339633 10838455326805902605504725)
                ·
                  refine ⟨254026296722013342316517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10838455326805902605504725 254026296722013342316517)
                  ·
                    rfl

theorem cell23_4452430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_4452430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452430 prefixEnd_4452430 := by exact prefixLift 4452430
  have htrace : WordTrace (prefixWord ++ tailWord_4452430) baseStart_4452430 baseEnd_4452430 := by
    simpa [prefixWord, tailWord_4452430, baseEnd_4452430] using wordTrace_append hprefix tailTrace_4452430
  have hstable : (prefixWord ++ tailWord_4452430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452430).length < 2 ^ (prefixWord ++ tailWord_4452430).sum := by decide
  have hdescent : baseEnd_4452430 < baseStart_4452430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452458 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_4452458 : Nat := 118140960795 + 4452458 * 2 ^ 59
def prefixEnd_4452458 : Nat := 4983230072969 + 3 ^ 40 * 4452458 * 2
def baseEnd_4452458 : Nat := 2286251047956445971298525

theorem tailTrace_4452458 : CollatzResearch.WordTrace tailWord_4452458 prefixEnd_4452458 2286251047956445971298525 := by
  unfold tailWord_4452458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40598621125878140032859507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108262989669008373420958685 40598621125878140032859507)
  ·
    refine ⟨60897931688817210049289261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40598621125878140032859507 60897931688817210049289261)
    ·
      refine ⟨22836724383306453768483473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60897931688817210049289261 22836724383306453768483473)
      ·
        refine ⟨17127543287479840326362605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22836724383306453768483473 17127543287479840326362605)
        ·
          refine ⟨6422828732804940122385977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17127543287479840326362605 6422828732804940122385977)
          ·
            refine ⟨4817121549603705091789483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6422828732804940122385977 4817121549603705091789483)
            ·
              refine ⟨7225682324405557637684225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817121549603705091789483 7225682324405557637684225)
              ·
                refine ⟨5419261743304168228263169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225682324405557637684225 5419261743304168228263169)
                ·
                  refine ⟨4064446307478126171197377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5419261743304168228263169 4064446307478126171197377)
                  ·
                    refine ⟨3048334730608594628398033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4064446307478126171197377 3048334730608594628398033)
                    ·
                      refine ⟨2286251047956445971298525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3048334730608594628398033 2286251047956445971298525)
                      ·
                        rfl

theorem cell23_4452458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_4452458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452458 prefixEnd_4452458 := by exact prefixLift 4452458
  have htrace : WordTrace (prefixWord ++ tailWord_4452458) baseStart_4452458 baseEnd_4452458 := by
    simpa [prefixWord, tailWord_4452458, baseEnd_4452458] using wordTrace_append hprefix tailTrace_4452458
  have hstable : (prefixWord ++ tailWord_4452458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452458).length < 2 ^ (prefixWord ++ tailWord_4452458).sum := by decide
  have hdescent : baseEnd_4452458 < baseStart_4452458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452514 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4452514 : Nat := 118140960795 + 4452514 * 2 ^ 59
def prefixEnd_4452514 : Nat := 4983230072969 + 3 ^ 40 * 4452514 * 2
def baseEnd_4452514 : Nat := 2286279802873097752198267

theorem tailTrace_4452514 : CollatzResearch.WordTrace tailWord_4452514 prefixEnd_4452514 2286279802873097752198267 := by
  unfold tailWord_4452514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40599131747827420423869149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108264351327539787796984397 40599131747827420423869149)
  ·
    refine ⟨15224674405435282658950931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40599131747827420423869149 15224674405435282658950931)
    ·
      refine ⟨22837011608152923988426397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15224674405435282658950931 22837011608152923988426397)
      ·
        refine ⟨8563879353057346495659899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22837011608152923988426397 8563879353057346495659899)
        ·
          refine ⟨12845819029586019743489849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563879353057346495659899 12845819029586019743489849)
          ·
            refine ⟨9634364272189514807617387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12845819029586019743489849 9634364272189514807617387)
            ·
              refine ⟨14451546408284272211426081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634364272189514807617387 14451546408284272211426081)
              ·
                refine ⟨10838659806213204158569561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14451546408284272211426081 10838659806213204158569561)
                ·
                  refine ⟨8128994854659903118927171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10838659806213204158569561 8128994854659903118927171)
                  ·
                    refine ⟨12193492281989854678390757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8128994854659903118927171 12193492281989854678390757)
                    ·
                      refine ⟨2286279802873097752198267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12193492281989854678390757 2286279802873097752198267)
                      ·
                        rfl

theorem cell23_4452514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4452514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452514 prefixEnd_4452514 := by exact prefixLift 4452514
  have htrace : WordTrace (prefixWord ++ tailWord_4452514) baseStart_4452514 baseEnd_4452514 := by
    simpa [prefixWord, tailWord_4452514, baseEnd_4452514] using wordTrace_append hprefix tailTrace_4452514
  have hstable : (prefixWord ++ tailWord_4452514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452514).length < 2 ^ (prefixWord ++ tailWord_4452514).sum := by decide
  have hdescent : baseEnd_4452514 < baseStart_4452514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452517 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_4452517 : Nat := 118140960795 + 4452517 * 2 ^ 59
def prefixEnd_4452517 : Nat := 4983230072969 + 3 ^ 40 * 4452517 * 2
def baseEnd_4452517 : Nat := 2286281343315061240460753

theorem tailTrace_4452517 : CollatzResearch.WordTrace tailWord_4452517 prefixEnd_4452517 2286281343315061240460753 := by
  unfold tailWord_4452517
  simp only [CollatzResearch.WordTrace]
  refine ⟨162396636410298813207835805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108264424273532542138557203 162396636410298813207835805)
  ·
    refine ⟨60898738653862054952938427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162396636410298813207835805 60898738653862054952938427)
    ·
      refine ⟨91348107980793082429407641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60898738653862054952938427 91348107980793082429407641)
      ·
        refine ⟨68511080985594811822055731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91348107980793082429407641 68511080985594811822055731)
        ·
          refine ⟨102766621478392217733083597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68511080985594811822055731 102766621478392217733083597)
          ·
            refine ⟨38537483054397081649906349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102766621478392217733083597 38537483054397081649906349)
            ·
              refine ⟨14451556145398905618714881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38537483054397081649906349 14451556145398905618714881)
              ·
                refine ⟨10838667109049179214036161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14451556145398905618714881 10838667109049179214036161)
                ·
                  refine ⟨8129000331786884410527121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10838667109049179214036161 8129000331786884410527121)
                  ·
                    refine ⟨6096750248840163307895341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8129000331786884410527121 6096750248840163307895341)
                    ·
                      refine ⟨2286281343315061240460753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6096750248840163307895341 2286281343315061240460753)
                      ·
                        rfl

theorem cell23_4452517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_4452517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452517 prefixEnd_4452517 := by exact prefixLift 4452517
  have htrace : WordTrace (prefixWord ++ tailWord_4452517) baseStart_4452517 baseEnd_4452517 := by
    simpa [prefixWord, tailWord_4452517, baseEnd_4452517] using wordTrace_append hprefix tailTrace_4452517
  have hstable : (prefixWord ++ tailWord_4452517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452517).length < 2 ^ (prefixWord ++ tailWord_4452517).sum := by decide
  have hdescent : baseEnd_4452517 < baseStart_4452517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452580 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_4452580 : Nat := 118140960795 + 4452580 * 2 ^ 59
def prefixEnd_4452580 : Nat := 4983230072969 + 3 ^ 40 * 4452580 * 2
def baseEnd_4452580 : Nat := 762104564198764831324321

theorem tailTrace_4452580 : CollatzResearch.WordTrace tailWord_4452580 prefixEnd_4452580 762104564198764831324321 := by
  unfold tailWord_4452580
  simp only [CollatzResearch.WordTrace]
  refine ⟨81199467104535287483689597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108265956139380383311586129 81199467104535287483689597)
  ·
    refine ⟨30449800164200732806383599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81199467104535287483689597 30449800164200732806383599)
    ·
      refine ⟨45674700246301099209575399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30449800164200732806383599 45674700246301099209575399)
      ·
        refine ⟨68512050369451648814363099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45674700246301099209575399 68512050369451648814363099)
        ·
          refine ⟨102768075554177473221544649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68512050369451648814363099 102768075554177473221544649)
          ·
            refine ⟨77076056665633104916158487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102768075554177473221544649 77076056665633104916158487)
            ·
              refine ⟨115614084998449657374237731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77076056665633104916158487 115614084998449657374237731)
              ·
                refine ⟨173421127497674486061356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115614084998449657374237731 173421127497674486061356597)
                ·
                  refine ⟨16258230702906983068252181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173421127497674486061356597 16258230702906983068252181)
                  ·
                    refine ⟨762104564198764831324321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16258230702906983068252181 762104564198764831324321)
                    ·
                      rfl

theorem cell23_4452580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_4452580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452580 prefixEnd_4452580 := by exact prefixLift 4452580
  have htrace : WordTrace (prefixWord ++ tailWord_4452580) baseStart_4452580 baseEnd_4452580 := by
    simpa [prefixWord, tailWord_4452580, baseEnd_4452580] using wordTrace_append hprefix tailTrace_4452580
  have hstable : (prefixWord ++ tailWord_4452580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452580).length < 2 ^ (prefixWord ++ tailWord_4452580).sum := by decide
  have hdescent : baseEnd_4452580 < baseStart_4452580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4452600 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_4452600 : Nat := 118140960795 + 4452600 * 2 ^ 59
def prefixEnd_4452600 : Nat := 4983230072969 + 3 ^ 40 * 4452600 * 2
def baseEnd_4452600 : Nat := 2286323962209384415722871

theorem tailTrace_4452600 : CollatzResearch.WordTrace tailWord_4452600 prefixEnd_4452600 2286323962209384415722871 := by
  unfold tailWord_4452600
  simp only [CollatzResearch.WordTrace]
  refine ⟨81199831834499059191553627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108266442445998745588738169 81199831834499059191553627)
  ·
    refine ⟨121799747751748588787330441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81199831834499059191553627 121799747751748588787330441)
    ·
      refine ⟨91349810813811441590497831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121799747751748588787330441 91349810813811441590497831)
      ·
        refine ⟨137024716220717162385746747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91349810813811441590497831 137024716220717162385746747)
        ·
          refine ⟨205537074331075743578620121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137024716220717162385746747 205537074331075743578620121)
          ·
            refine ⟨154152805748306807683965091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205537074331075743578620121 154152805748306807683965091)
            ·
              refine ⟨231229208622460211525947637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154152805748306807683965091 231229208622460211525947637)
              ·
                refine ⟨21677738308355644830557591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231229208622460211525947637 21677738308355644830557591)
                ·
                  refine ⟨32516607462533467245836387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21677738308355644830557591 32516607462533467245836387)
                  ·
                    refine ⟨48774911193800200868754581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32516607462533467245836387 48774911193800200868754581)
                    ·
                      refine ⟨2286323962209384415722871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48774911193800200868754581 2286323962209384415722871)
                      ·
                        rfl

theorem cell23_4452600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_4452600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4452600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4452600 prefixEnd_4452600 := by exact prefixLift 4452600
  have htrace : WordTrace (prefixWord ++ tailWord_4452600) baseStart_4452600 baseEnd_4452600 := by
    simpa [prefixWord, tailWord_4452600, baseEnd_4452600] using wordTrace_append hprefix tailTrace_4452600
  have hstable : (prefixWord ++ tailWord_4452600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4452600).length < 2 ^ (prefixWord ++ tailWord_4452600).sum := by decide
  have hdescent : baseEnd_4452600 < baseStart_4452600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4452600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
